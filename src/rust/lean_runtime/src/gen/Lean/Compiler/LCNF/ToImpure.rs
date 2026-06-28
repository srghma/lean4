// Lean compiler output
// Module: Lean.Compiler.LCNF.ToImpure
// Imports: Lean.Compiler.LCNF.ToImpureType Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PhaseExt Init.Data.Format.Macro
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_get___boxed, l_StateRefT_x27_instMonad___aux__13___boxed,
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_instInhabited, l_Array_zip___redArg};
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadLift___lam__0___boxed, l_instInhabitedOfMonad___redArg,
    l_instMonadLiftT___lam__0___boxed, l_instMonadLiftTOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Init::System::IO::{
    l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, l_instMonadEIO,
    l_instMonadLiftBaseIOEIO___lam__0___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_CtorInfo_type, l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit,
    l_Lean_Compiler_LCNF_instInhabitedAlt_default__1,
    l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
    l_Lean_Compiler_LCNF_instInhabitedParam_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp,
    l_Lean_Compiler_LCNF_getPurity___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, l_Lean_Compiler_LCNF_mkLetDecl,
    l_Lean_Compiler_LCNF_mkReturnErased, l_Lean_Compiler_LCNF_normFVarImp___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::{
    l_Lean_Compiler_LCNF_LCtx_addFunDecl, l_Lean_Compiler_LCNF_LCtx_addLetDecl,
    l_Lean_Compiler_LCNF_LCtx_addParam, l_Lean_Compiler_LCNF_LCtx_toLocalContext,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_Decl_saveImpure___redArg,
    l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg,
    l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg, runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::ToImpureType::{
    initialize_Lean_Compiler_LCNF_ToImpureType, l_Lean_Compiler_LCNF_getCtorLayout,
    l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f, l_Lean_Compiler_LCNF_nameToImpureType,
    l_Lean_Compiler_LCNF_toImpureType, runtime_initialize_Lean_Compiler_LCNF_ToImpureType,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed,
    l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar, l_Lean_Expr_isErased, l_Lean_Expr_isVoid,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_liftIOCore___boxed,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn,
    l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash, l_Lean_instInhabitedExpr,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_6, lean_box, lean_closure_set, lean_cstr_to_nat, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 103, 103, 101, 100, 95, 114, 101, 116, 117, 114, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,1593025795173086250 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [109, 97, 114, 107, 32, 101, 120, 116, 101, 114, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 97, 108, 119, 97, 121, 115, 32, 114, 101, 116, 117, 114, 110, 32, 116, 97, 103, 103, 101, 100, 32, 118, 97, 108, 117, 101, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 111, 73, 109, 112, 117, 114, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,4966364398685493096 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,14379249816071646785 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,18367342368312912612 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,2907737383505607502 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,18190660011109909687 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [116, 97, 103, 103, 101, 100, 82, 101, 116, 117, 114, 110, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,18073347029703811059 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value: LeanStringObject<150> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 150, m_capacity: 150, m_length: 149, m_data: [77, 97, 114, 107, 115, 32, 97, 110, 32, 101, 120, 116, 101, 114, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 98, 101, 32, 103, 117, 97, 114, 97, 110, 116, 101, 101, 100, 32, 116, 111, 32, 97, 108, 119, 97, 121, 115, 32, 114, 101, 116, 117, 114, 110, 32, 116, 97, 103, 103, 101, 100, 32, 118, 97, 108, 117, 101, 115, 46, 10, 84, 104, 105, 115, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 32, 105, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 111, 112, 116, 105, 109, 105, 122, 101, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 99, 111, 117, 110, 116, 105, 110, 103, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 109, 112, 105, 108, 101, 114, 46, 10, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 18 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 93 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 93 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_liftIOCore___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftBaseIOEIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value: LeanClosureObject<4> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_StateRefT_x27_get___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value) as *mut LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 99, 69, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value) as *mut LeanObject,381462102099548843 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 83, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value) as *mut LeanObject,17712594561405737325 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 99, 86, 111, 105, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value) as *mut LeanObject,12548675615898448964 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value
) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value: LeanStringObject<93> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 108, 111, 119, 101, 114, 82, 101, 115, 117, 108, 116, 84, 121, 112, 101, 46, 114, 101, 115, 117, 108, 116, 84, 121, 112, 101, 70, 111, 114, 65, 114, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 97, 114, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 111, 98, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value) as *mut LeanObject,930430701391226905 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 103, 103, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value) as *mut LeanObject,13921617720798624167 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 98, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value) as *mut LeanObject,6552590064380865520 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value) as *mut LeanObject,15764114953608429200 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value) as *mut LeanObject,9755723410228041222 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value) as *mut LeanObject,13474504806189678690 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 54, 52, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value) as *mut LeanObject,2954612489107370298 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 111, 102, 32, 110, 111, 110, 45, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 108, 111, 119, 101, 114, 76, 101, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 118, 101, 114, 97, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 116, 111, 32, 117, 110, 98, 111, 117, 110, 100, 32, 110, 97, 109, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [84, 111, 73, 109, 112, 117, 114, 101, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 117, 115, 101, 32, 111, 102, 32, 110, 111, 110, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 59, 32, 112, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 116, 104, 105, 115, 32, 105, 115, 115, 117, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value
) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 111, 114, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [96, 32, 121, 101, 116, 44, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103, 32, 39, 109, 97, 116, 99, 104, 32, 46, 46, 46, 32, 119, 105, 116, 104, 39, 32, 97, 110, 100, 47, 111, 114, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 38, m_data: [97, 108, 108, 32, 108, 111, 99, 97, 108, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 206, 187, 45, 108, 105, 102, 116, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value: LeanStringObject<72> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 100, 101, 46, 116, 111, 73, 109, 112, 117, 114, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 46, 97, 108, 116, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 49, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 116, 111, 114, 78, 97, 109, 101, 32, 61, 61, 32, 105, 110, 102, 111, 46, 99, 116, 111, 114, 78, 97, 109, 101, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_value: LeanStringObject<52> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 110, 102, 111, 46, 102, 105, 101, 108, 100, 73, 100, 120, 32, 60, 32, 112, 115, 46, 115, 105, 122, 101, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [109, 105, 115, 109, 97, 116, 99, 104, 101, 100, 32, 102, 105, 101, 108, 100, 115, 32, 97, 110, 100, 32, 112, 97, 114, 97, 109, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value: LeanStringObject<76> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 65, 108, 116, 46, 116, 111, 73, 109, 112, 117, 114, 101, 46, 108, 111, 111, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [69, 114, 114, 111, 114, 32, 119, 104, 105, 108, 101, 32, 99, 111, 109, 112, 105, 108, 105, 110, 103, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 39, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [39, 58, 32, 64, 91, 116, 97, 103, 103, 101, 100, 95, 114, 101, 116, 117, 114, 110, 93, 32, 105, 115, 32, 111, 110, 108, 121, 32, 118, 97, 108, 105, 100, 32, 102, 111, 114, 32, 101, 120, 116, 101, 114, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [64, 91, 116, 97, 103, 103, 101, 100, 95, 114, 101, 116, 117, 114, 110, 93, 32, 111, 110, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 39, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [39, 32, 119, 105, 116, 104, 32, 115, 99, 97, 108, 97, 114, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toImpure___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_toImpure___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_toImpure___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_toImpure___closed__1_value: LeanStringObject<9> =
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
        m_data: [116, 111, 73, 109, 112, 117, 114, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_toImpure___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_toImpure___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__1_value) as *mut LeanObject,
        17827820499012269448 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_toImpure___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_toImpure___closed__3_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__0_value) as *mut LeanObject,
        66049 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_toImpure___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_toImpure: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__3_value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpure___closed__1_value) as *mut LeanObject,4012882663848748230 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,15413550040146560646 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,17530674738139146295 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,14262752522474704330 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,14073625359394912280 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,11792518438694555345 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value) as *mut LeanObject,1672682711785709656 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,((( 6355896 as usize) << 1) | 1) as *mut LeanObject,11489881094049781737 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,12372414368286703290 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,4669787044454536070 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,6615778342409581959 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(
    mut v_x_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
    mut v___y_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    v___x_3055_ = lean_box(0);
    v___x_3056_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3056_, 0, v___x_3055_);
    return v___x_3056_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(
    mut v_x_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3061_: *mut LeanObject = core::ptr::null_mut();
    v_res_3061_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(v_x_3057_, v___y_3058_, v___y_3059_);
    lean_dec(v___y_3059_);
    lean_dec_ref(v___y_3058_);
    lean_dec(v_x_3057_);
    return v_res_3061_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    v___f_3104_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_;
    v___x_3105_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_;
    v___x_3106_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_;
    v___x_3107_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_;
    v___x_3108_ = 0;
    v___x_3109_ = lean_box(2);
    v___x_3110_ = l_Lean_registerTagAttribute(
        v___x_3105_,
        v___x_3106_,
        v___f_3104_,
        v___x_3107_,
        v___x_3108_,
        v___x_3109_,
    );
    return v___x_3110_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(
    mut v_a_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3112_: *mut LeanObject = core::ptr::null_mut();
    v_res_3112_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
    return v_res_3112_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    v___x_3115_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_;
    v___x_3116_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0;
    v___x_3117_ = l_Lean_addBuiltinDocString(v___x_3115_, v___x_3116_);
    return v___x_3117_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(
    mut v_a_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3119_: *mut LeanObject = core::ptr::null_mut();
    v_res_3119_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
    return v_res_3119_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    v___x_3146_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_;
    v___x_3147_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6;
    v___x_3148_ = l_Lean_addBuiltinDeclarationRanges(v___x_3146_, v___x_3147_);
    return v___x_3148_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___boxed(
    mut v_a_3149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3150_: *mut LeanObject = core::ptr::null_mut();
    v_res_3150_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
    return v_res_3150_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(
    mut v_____do__lift_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
    mut v___y_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subst_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    v_subst_3158_ = lean_ctor_get(v_____do__lift_3151_, 0);
    lean_inc_ref(v_subst_3158_);
    v___x_3159_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3159_, 0, v_subst_3158_);
    return v___x_3159_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(
    mut v_____do__lift_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3167_: *mut LeanObject = core::ptr::null_mut();
    v_res_3167_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
    lean_dec(v___y_3165_);
    lean_dec_ref(v___y_3164_);
    lean_dec(v___y_3163_);
    lean_dec_ref(v___y_3162_);
    lean_dec(v___y_3161_);
    lean_dec_ref(v_____do__lift_3160_);
    return v_res_3167_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0()
-> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_instMonadEIO(lean_box(0));
    return v___x_3168_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1()
-> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    v___x_3169_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0);
    v___x_3170_ = l_StateRefT_x27_instMonad___redArg(v___x_3169_);
    return v___x_3170_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue()
-> *mut LeanObject {
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v_toFunctor_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___f_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3244_: u8 = 0;
    let mut v_unused_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3246_: u8 = 0;
    let mut v_unused_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3199_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
                v_toApplicative_3200_ = lean_ctor_get(v___x_3199_, 0);
                v_toFunctor_3201_ = lean_ctor_get(v_toApplicative_3200_, 0);
                v_toSeq_3202_ = lean_ctor_get(v_toApplicative_3200_, 2);
                v_toSeqLeft_3203_ = lean_ctor_get(v_toApplicative_3200_, 3);
                v_toSeqRight_3204_ = lean_ctor_get(v_toApplicative_3200_, 4);
                v___f_3205_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2;
                v___f_3206_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3;
                lean_inc_ref_n(v_toFunctor_3201_, 2);
                v___f_3207_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3207_, 0, v_toFunctor_3201_);
                v___f_3208_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3208_, 0, v_toFunctor_3201_);
                v___x_3209_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3209_, 0, v___f_3207_);
                lean_ctor_set(v___x_3209_, 1, v___f_3208_);
                lean_inc(v_toSeqRight_3204_);
                v___f_3210_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3210_, 0, v_toSeqRight_3204_);
                lean_inc(v_toSeqLeft_3203_);
                v___f_3211_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3211_, 0, v_toSeqLeft_3203_);
                lean_inc(v_toSeq_3202_);
                v___f_3212_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3212_, 0, v_toSeq_3202_);
                v___x_3213_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3213_, 0, v___x_3209_);
                lean_ctor_set(v___x_3213_, 1, v___f_3205_);
                lean_ctor_set(v___x_3213_, 2, v___f_3212_);
                lean_ctor_set(v___x_3213_, 3, v___f_3211_);
                lean_ctor_set(v___x_3213_, 4, v___f_3210_);
                v___x_3214_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3214_, 0, v___x_3213_);
                lean_ctor_set(v___x_3214_, 1, v___f_3206_);
                v___x_3215_ = l_StateRefT_x27_instMonad___redArg(v___x_3214_);
                v_toApplicative_3216_ = lean_ctor_get(v___x_3215_, 0);
                v_isSharedCheck_3246_ = (!lean_is_exclusive(v___x_3215_)) as u8;
                if v_isSharedCheck_3246_ == 0 {
                    v_unused_3247_ = lean_ctor_get(v___x_3215_, 1);
                    lean_dec(v_unused_3247_);
                    v___x_3218_ = v___x_3215_;
                    v_isShared_3219_ = v_isSharedCheck_3246_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3216_);
                    lean_dec(v___x_3215_);
                    v___x_3218_ = lean_box(0);
                    v_isShared_3219_ = v_isSharedCheck_3246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3220_ = lean_ctor_get(v_toApplicative_3216_, 0);
                v_toSeq_3221_ = lean_ctor_get(v_toApplicative_3216_, 2);
                v_toSeqLeft_3222_ = lean_ctor_get(v_toApplicative_3216_, 3);
                v_toSeqRight_3223_ = lean_ctor_get(v_toApplicative_3216_, 4);
                v_isSharedCheck_3244_ = (!lean_is_exclusive(v_toApplicative_3216_)) as u8;
                if v_isSharedCheck_3244_ == 0 {
                    v_unused_3245_ = lean_ctor_get(v_toApplicative_3216_, 1);
                    lean_dec(v_unused_3245_);
                    v___x_3225_ = v_toApplicative_3216_;
                    v_isShared_3226_ = v_isSharedCheck_3244_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3223_);
                    lean_inc(v_toSeqLeft_3222_);
                    lean_inc(v_toSeq_3221_);
                    lean_inc(v_toFunctor_3220_);
                    lean_dec(v_toApplicative_3216_);
                    v___x_3225_ = lean_box(0);
                    v_isShared_3226_ = v_isSharedCheck_3244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3227_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4;
                v___f_3228_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5;
                v___f_3229_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6;
                lean_inc_ref(v_toFunctor_3220_);
                v___f_3230_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3230_, 0, v_toFunctor_3220_);
                v___f_3231_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3231_, 0, v_toFunctor_3220_);
                v___x_3232_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3232_, 0, v___f_3230_);
                lean_ctor_set(v___x_3232_, 1, v___f_3231_);
                v___f_3233_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3233_, 0, v_toSeqRight_3223_);
                v___f_3234_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3234_, 0, v_toSeqLeft_3222_);
                v___f_3235_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3235_, 0, v_toSeq_3221_);
                if v_isShared_3226_ == 0 {
                    lean_ctor_set(v___x_3225_, 4, v___f_3233_);
                    lean_ctor_set(v___x_3225_, 3, v___f_3234_);
                    lean_ctor_set(v___x_3225_, 2, v___f_3235_);
                    lean_ctor_set(v___x_3225_, 1, v___f_3228_);
                    lean_ctor_set(v___x_3225_, 0, v___x_3232_);
                    v___x_3237_ = v___x_3225_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3232_);
                    lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___f_3228_);
                    lean_ctor_set(v_reuseFailAlloc_3243_, 2, v___f_3235_);
                    lean_ctor_set(v_reuseFailAlloc_3243_, 3, v___f_3234_);
                    lean_ctor_set(v_reuseFailAlloc_3243_, 4, v___f_3233_);
                    v___x_3237_ = v_reuseFailAlloc_3243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3219_ == 0 {
                    lean_ctor_set(v___x_3218_, 1, v___f_3229_);
                    lean_ctor_set(v___x_3218_, 0, v___x_3237_);
                    v___x_3239_ = v___x_3218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3237_);
                    lean_ctor_set(v_reuseFailAlloc_3242_, 1, v___f_3229_);
                    v___x_3239_ = v_reuseFailAlloc_3242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3240_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18;
                v___x_3241_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
                    9,
                    8,
                );
                lean_closure_set(v___x_3241_, 0, lean_box(0));
                lean_closure_set(v___x_3241_, 1, lean_box(0));
                lean_closure_set(v___x_3241_, 2, lean_box(0));
                lean_closure_set(v___x_3241_, 3, v___x_3239_);
                lean_closure_set(v___x_3241_, 4, lean_box(0));
                lean_closure_set(v___x_3241_, 5, lean_box(0));
                lean_closure_set(v___x_3241_, 6, v___x_3240_);
                lean_closure_set(v___x_3241_, 7, v___f_3227_);
                return v___x_3241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(
    mut v_f_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3255_ = lean_st_ref_take(v___y_3249_);
                v_subst_3256_ = lean_ctor_get(v___x_3255_, 0);
                v_jpParamMask_3257_ = lean_ctor_get(v___x_3255_, 1);
                v_isSharedCheck_3268_ = (!lean_is_exclusive(v___x_3255_)) as u8;
                if v_isSharedCheck_3268_ == 0 {
                    v___x_3259_ = v___x_3255_;
                    v_isShared_3260_ = v_isSharedCheck_3268_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_jpParamMask_3257_);
                    lean_inc(v_subst_3256_);
                    lean_dec(v___x_3255_);
                    v___x_3259_ = lean_box(0);
                    v_isShared_3260_ = v_isSharedCheck_3268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3261_ = lean_apply_1(v_f_3248_, v_subst_3256_);
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 0, v___x_3261_);
                    v___x_3263_ = v___x_3259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3261_);
                    lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_jpParamMask_3257_);
                    v___x_3263_ = v_reuseFailAlloc_3267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3264_ = lean_st_ref_set(v___y_3249_, v___x_3263_);
                v___x_3265_ = lean_box(0);
                v___x_3266_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3266_, 0, v___x_3265_);
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(
    mut v_f_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
    mut v___y_3271_: *mut LeanObject,
    mut v___y_3272_: *mut LeanObject,
    mut v___y_3273_: *mut LeanObject,
    mut v___y_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3276_: *mut LeanObject = core::ptr::null_mut();
    v_res_3276_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
    lean_dec(v___y_3274_);
    lean_dec_ref(v___y_3273_);
    lean_dec(v___y_3272_);
    lean_dec_ref(v___y_3271_);
    lean_dec(v___y_3270_);
    return v_res_3276_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(
    mut v_a_3279_: *mut LeanObject,
    mut v_b_3280_: *mut LeanObject,
    mut v_x_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3288_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3281_) == 0 {
                    lean_dec(v_b_3280_);
                    lean_dec(v_a_3279_);
                    return v_x_3281_;
                } else {
                    v_key_3282_ = lean_ctor_get(v_x_3281_, 0);
                    v_value_3283_ = lean_ctor_get(v_x_3281_, 1);
                    v_tail_3284_ = lean_ctor_get(v_x_3281_, 2);
                    v_isSharedCheck_3296_ = (!lean_is_exclusive(v_x_3281_)) as u8;
                    if v_isSharedCheck_3296_ == 0 {
                        v___x_3286_ = v_x_3281_;
                        v_isShared_3287_ = v_isSharedCheck_3296_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3284_);
                        lean_inc(v_value_3283_);
                        lean_inc(v_key_3282_);
                        lean_dec(v_x_3281_);
                        v___x_3286_ = lean_box(0);
                        v_isShared_3287_ = v_isSharedCheck_3296_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3288_ = l_Lean_instBEqFVarId_beq(v_key_3282_, v_a_3279_);
                if v___x_3288_ == 0 {
                    v___x_3289_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_3279_, v_b_3280_, v_tail_3284_);
                    if v_isShared_3287_ == 0 {
                        lean_ctor_set(v___x_3286_, 2, v___x_3289_);
                        v___x_3291_ = v___x_3286_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_key_3282_);
                        lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_value_3283_);
                        lean_ctor_set(v_reuseFailAlloc_3292_, 2, v___x_3289_);
                        v___x_3291_ = v_reuseFailAlloc_3292_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3283_);
                    lean_dec(v_key_3282_);
                    if v_isShared_3287_ == 0 {
                        lean_ctor_set(v___x_3286_, 1, v_b_3280_);
                        lean_ctor_set(v___x_3286_, 0, v_a_3279_);
                        v___x_3294_ = v___x_3286_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3279_);
                        lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_b_3280_);
                        lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_tail_3284_);
                        v___x_3294_ = v_reuseFailAlloc_3295_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3291_;
            }
            3 => {
                return v___x_3294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_3297_: *mut LeanObject,
    mut v_x_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u64 = 0;
    let mut v___x_3307_: u64 = 0;
    let mut v___x_3308_: u64 = 0;
    let mut v_fold_3309_: u64 = 0;
    let mut v___x_3310_: u64 = 0;
    let mut v___x_3311_: u64 = 0;
    let mut v___x_3312_: u64 = 0;
    let mut v___x_3313_: usize = 0;
    let mut v___x_3314_: usize = 0;
    let mut v___x_3315_: usize = 0;
    let mut v___x_3316_: usize = 0;
    let mut v___x_3317_: usize = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3298_) == 0 {
                    return v_x_3297_;
                } else {
                    v_key_3299_ = lean_ctor_get(v_x_3298_, 0);
                    v_value_3300_ = lean_ctor_get(v_x_3298_, 1);
                    v_tail_3301_ = lean_ctor_get(v_x_3298_, 2);
                    v_isSharedCheck_3324_ = (!lean_is_exclusive(v_x_3298_)) as u8;
                    if v_isSharedCheck_3324_ == 0 {
                        v___x_3303_ = v_x_3298_;
                        v_isShared_3304_ = v_isSharedCheck_3324_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3301_);
                        lean_inc(v_value_3300_);
                        lean_inc(v_key_3299_);
                        lean_dec(v_x_3298_);
                        v___x_3303_ = lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3305_ = lean_array_get_size(v_x_3297_);
                v___x_3306_ = l_Lean_instHashableFVarId_hash(v_key_3299_);
                v___x_3307_ = 32u64;
                v___x_3308_ = lean_uint64_shift_right(v___x_3306_, v___x_3307_);
                v_fold_3309_ = lean_uint64_xor(v___x_3306_, v___x_3308_);
                v___x_3310_ = 16u64;
                v___x_3311_ = lean_uint64_shift_right(v_fold_3309_, v___x_3310_);
                v___x_3312_ = lean_uint64_xor(v_fold_3309_, v___x_3311_);
                v___x_3313_ = lean_uint64_to_usize(v___x_3312_);
                v___x_3314_ = lean_usize_of_nat(v___x_3305_);
                v___x_3315_ = 1usize;
                v___x_3316_ = lean_usize_sub(v___x_3314_, v___x_3315_);
                v___x_3317_ = lean_usize_land(v___x_3313_, v___x_3316_);
                v___x_3318_ = lean_array_uget_borrowed(v_x_3297_, v___x_3317_);
                lean_inc(v___x_3318_);
                if v_isShared_3304_ == 0 {
                    lean_ctor_set(v___x_3303_, 2, v___x_3318_);
                    v___x_3320_ = v___x_3303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_key_3299_);
                    lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_value_3300_);
                    lean_ctor_set(v_reuseFailAlloc_3323_, 2, v___x_3318_);
                    v___x_3320_ = v_reuseFailAlloc_3323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3321_ = lean_array_uset(v_x_3297_, v___x_3317_, v___x_3320_);
                v_x_3297_ = v___x_3321_;
                v_x_3298_ = v_tail_3301_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(
    mut v_i_3325_: *mut LeanObject,
    mut v_source_3326_: *mut LeanObject,
    mut v_target_3327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v_es_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_array_get_size(v_source_3326_);
                v___x_3329_ = lean_nat_dec_lt(v_i_3325_, v___x_3328_);
                if v___x_3329_ == 0 {
                    lean_dec_ref(v_source_3326_);
                    lean_dec(v_i_3325_);
                    return v_target_3327_;
                } else {
                    v_es_3330_ = lean_array_fget(v_source_3326_, v_i_3325_);
                    v___x_3331_ = lean_box(0);
                    v_source_3332_ = lean_array_fset(v_source_3326_, v_i_3325_, v___x_3331_);
                    v_target_3333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3327_, v_es_3330_);
                    v___x_3334_ = lean_unsigned_to_nat(1);
                    v___x_3335_ = lean_nat_add(v_i_3325_, v___x_3334_);
                    lean_dec(v_i_3325_);
                    v_i_3325_ = v___x_3335_;
                    v_source_3326_ = v_source_3332_;
                    v_target_3327_ = v_target_3333_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(
    mut v_data_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    v___x_3338_ = lean_array_get_size(v_data_3337_);
    v___x_3339_ = lean_unsigned_to_nat(2);
    v_nbuckets_3340_ = lean_nat_mul(v___x_3338_, v___x_3339_);
    v___x_3341_ = lean_unsigned_to_nat(0);
    v___x_3342_ = lean_box(0);
    v___x_3343_ = lean_mk_array(v_nbuckets_3340_, v___x_3342_);
    v___x_3344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v___x_3341_, v_data_3337_, v___x_3343_);
    return v___x_3344_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(
    mut v_a_3345_: *mut LeanObject,
    mut v_x_3346_: *mut LeanObject,
) -> u8 {
    let mut v___x_3347_: u8 = 0;
    let mut v_key_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3346_) == 0 {
                    v___x_3347_ = 0;
                    return v___x_3347_;
                } else {
                    v_key_3348_ = lean_ctor_get(v_x_3346_, 0);
                    v_tail_3349_ = lean_ctor_get(v_x_3346_, 2);
                    v___x_3350_ = l_Lean_instBEqFVarId_beq(v_key_3348_, v_a_3345_);
                    if v___x_3350_ == 0 {
                        v_x_3346_ = v_tail_3349_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3350_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(
    mut v_a_3352_: *mut LeanObject,
    mut v_x_3353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3354_: u8 = 0;
    let mut v_r_3355_: *mut LeanObject = core::ptr::null_mut();
    v_res_3354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_3352_, v_x_3353_);
    lean_dec(v_x_3353_);
    lean_dec(v_a_3352_);
    v_r_3355_ = lean_box((v_res_3354_) as usize);
    return v_r_3355_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(
    mut v_m_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
    mut v_b_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u64 = 0;
    let mut v___x_3366_: u64 = 0;
    let mut v___x_3367_: u64 = 0;
    let mut v_fold_3368_: u64 = 0;
    let mut v___x_3369_: u64 = 0;
    let mut v___x_3370_: u64 = 0;
    let mut v___x_3371_: u64 = 0;
    let mut v___x_3372_: usize = 0;
    let mut v___x_3373_: usize = 0;
    let mut v___x_3374_: usize = 0;
    let mut v___x_3375_: usize = 0;
    let mut v___x_3376_: usize = 0;
    let mut v_bkt_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: u8 = 0;
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: u8 = 0;
    let mut v_val_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3359_ = lean_ctor_get(v_m_3356_, 0);
                v_buckets_3360_ = lean_ctor_get(v_m_3356_, 1);
                v_isSharedCheck_3403_ = (!lean_is_exclusive(v_m_3356_)) as u8;
                if v_isSharedCheck_3403_ == 0 {
                    v___x_3362_ = v_m_3356_;
                    v_isShared_3363_ = v_isSharedCheck_3403_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3360_);
                    lean_inc(v_size_3359_);
                    lean_dec(v_m_3356_);
                    v___x_3362_ = lean_box(0);
                    v_isShared_3363_ = v_isSharedCheck_3403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3364_ = lean_array_get_size(v_buckets_3360_);
                v___x_3365_ = l_Lean_instHashableFVarId_hash(v_a_3357_);
                v___x_3366_ = 32u64;
                v___x_3367_ = lean_uint64_shift_right(v___x_3365_, v___x_3366_);
                v_fold_3368_ = lean_uint64_xor(v___x_3365_, v___x_3367_);
                v___x_3369_ = 16u64;
                v___x_3370_ = lean_uint64_shift_right(v_fold_3368_, v___x_3369_);
                v___x_3371_ = lean_uint64_xor(v_fold_3368_, v___x_3370_);
                v___x_3372_ = lean_uint64_to_usize(v___x_3371_);
                v___x_3373_ = lean_usize_of_nat(v___x_3364_);
                v___x_3374_ = 1usize;
                v___x_3375_ = lean_usize_sub(v___x_3373_, v___x_3374_);
                v___x_3376_ = lean_usize_land(v___x_3372_, v___x_3375_);
                v_bkt_3377_ = lean_array_uget_borrowed(v_buckets_3360_, v___x_3376_);
                v___x_3378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_3357_, v_bkt_3377_);
                if v___x_3378_ == 0 {
                    v___x_3379_ = lean_unsigned_to_nat(1);
                    v_size_x27_3380_ = lean_nat_add(v_size_3359_, v___x_3379_);
                    lean_dec(v_size_3359_);
                    lean_inc(v_bkt_3377_);
                    v___x_3381_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3381_, 0, v_a_3357_);
                    lean_ctor_set(v___x_3381_, 1, v_b_3358_);
                    lean_ctor_set(v___x_3381_, 2, v_bkt_3377_);
                    v_buckets_x27_3382_ =
                        lean_array_uset(v_buckets_3360_, v___x_3376_, v___x_3381_);
                    v___x_3383_ = lean_unsigned_to_nat(4);
                    v___x_3384_ = lean_nat_mul(v_size_x27_3380_, v___x_3383_);
                    v___x_3385_ = lean_unsigned_to_nat(3);
                    v___x_3386_ = lean_nat_div(v___x_3384_, v___x_3385_);
                    lean_dec(v___x_3384_);
                    v___x_3387_ = lean_array_get_size(v_buckets_x27_3382_);
                    v___x_3388_ = lean_nat_dec_le(v___x_3386_, v___x_3387_);
                    lean_dec(v___x_3386_);
                    if v___x_3388_ == 0 {
                        v_val_3389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_buckets_x27_3382_);
                        if v_isShared_3363_ == 0 {
                            lean_ctor_set(v___x_3362_, 1, v_val_3389_);
                            lean_ctor_set(v___x_3362_, 0, v_size_x27_3380_);
                            v___x_3391_ = v___x_3362_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_size_x27_3380_);
                            lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_val_3389_);
                            v___x_3391_ = v_reuseFailAlloc_3392_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3363_ == 0 {
                            lean_ctor_set(v___x_3362_, 1, v_buckets_x27_3382_);
                            lean_ctor_set(v___x_3362_, 0, v_size_x27_3380_);
                            v___x_3394_ = v___x_3362_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_size_x27_3380_);
                            lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_buckets_x27_3382_);
                            v___x_3394_ = v_reuseFailAlloc_3395_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3377_);
                    v___x_3396_ = lean_box(0);
                    v_buckets_x27_3397_ =
                        lean_array_uset(v_buckets_3360_, v___x_3376_, v___x_3396_);
                    v___x_3398_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_3357_, v_b_3358_, v_bkt_3377_);
                    v___x_3399_ = lean_array_uset(v_buckets_x27_3397_, v___x_3376_, v___x_3398_);
                    if v_isShared_3363_ == 0 {
                        lean_ctor_set(v___x_3362_, 1, v___x_3399_);
                        v___x_3401_ = v___x_3362_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_size_3359_);
                        lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___x_3399_);
                        v___x_3401_ = v_reuseFailAlloc_3402_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3391_;
            }
            3 => {
                return v___x_3394_;
            }
            4 => {
                return v___x_3401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(
    mut v_p_3404_: *mut LeanObject,
    mut v_a_3405_: *mut LeanObject,
    mut v_a_3406_: *mut LeanObject,
    mut v_a_3407_: *mut LeanObject,
    mut v_a_3408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_3413_: u8 = 0;
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3421_: u8 = 0;
    let mut v___y_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3429_: u8 = 0;
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v___y_3444_: u8 = 0;
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3457_: u8 = 0;
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: u8 = 0;
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut v_a_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_3410_ = lean_ctor_get(v_p_3404_, 0);
                v_binderName_3411_ = lean_ctor_get(v_p_3404_, 1);
                v_type_3412_ = lean_ctor_get(v_p_3404_, 2);
                v_borrow_3413_ = lean_ctor_get_uint8(
                    v_p_3404_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_3469_ = (!lean_is_exclusive(v_p_3404_)) as u8;
                if v_isSharedCheck_3469_ == 0 {
                    v___x_3415_ = v_p_3404_;
                    v_isShared_3416_ = v_isSharedCheck_3469_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_type_3412_);
                    lean_inc(v_binderName_3411_);
                    lean_inc(v_fvarId_3410_);
                    lean_dec(v_p_3404_);
                    v___x_3415_ = lean_box(0);
                    v_isShared_3416_ = v_isSharedCheck_3469_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3417_ = l_Lean_Compiler_LCNF_toImpureType(v_type_3412_, v_a_3407_, v_a_3408_);
                if lean_obj_tag(v___x_3417_) == 0 {
                    v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
                    v_isSharedCheck_3460_ = (!lean_is_exclusive(v___x_3417_)) as u8;
                    if v_isSharedCheck_3460_ == 0 {
                        v___x_3420_ = v___x_3417_;
                        v_isShared_3421_ = v_isSharedCheck_3460_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3418_);
                        lean_dec(v___x_3417_);
                        v___x_3420_ = lean_box(0);
                        v_isShared_3421_ = v_isSharedCheck_3460_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3415_);
                    lean_dec(v_binderName_3411_);
                    lean_dec(v_fvarId_3410_);
                    v_a_3461_ = lean_ctor_get(v___x_3417_, 0);
                    v_isSharedCheck_3468_ = (!lean_is_exclusive(v___x_3417_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3463_ = v___x_3417_;
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3461_);
                        lean_dec(v___x_3417_);
                        v___x_3463_ = lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3458_ = l_Lean_Expr_isVoid(v_a_3418_);
                if v___x_3458_ == 0 {
                    v___x_3459_ = l_Lean_Expr_isErased(v_a_3418_);
                    v___y_3444_ = v___x_3459_;
                    state = 8;
                    continue;
                } else {
                    v___y_3444_ = v___x_3458_;
                    state = 8;
                    continue;
                }
            }
            3 => {
                v___x_3424_ = lean_st_ref_take(v___y_3423_);
                v_lctx_3425_ = lean_ctor_get(v___x_3424_, 0);
                v_nextIdx_3426_ = lean_ctor_get(v___x_3424_, 1);
                v_isSharedCheck_3442_ = (!lean_is_exclusive(v___x_3424_)) as u8;
                if v_isSharedCheck_3442_ == 0 {
                    v___x_3428_ = v___x_3424_;
                    v_isShared_3429_ = v_isSharedCheck_3442_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_nextIdx_3426_);
                    lean_inc(v_lctx_3425_);
                    lean_dec(v___x_3424_);
                    v___x_3428_ = lean_box(0);
                    v_isShared_3429_ = v_isSharedCheck_3442_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3430_ = 1;
                if v_isShared_3416_ == 0 {
                    lean_ctor_set(v___x_3415_, 2, v_a_3418_);
                    v___x_3432_ = v___x_3415_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_fvarId_3410_);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_binderName_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 2, v_a_3418_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3441_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_borrow_3413_,
                    );
                    v___x_3432_ = v_reuseFailAlloc_3441_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3432_);
                v___x_3433_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v___x_3430_, v_lctx_3425_, v___x_3432_);
                if v_isShared_3429_ == 0 {
                    lean_ctor_set(v___x_3428_, 0, v___x_3433_);
                    v___x_3435_ = v___x_3428_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3433_);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_nextIdx_3426_);
                    v___x_3435_ = v_reuseFailAlloc_3440_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3436_ = lean_st_ref_set(v___y_3423_, v___x_3435_);
                if v_isShared_3421_ == 0 {
                    lean_ctor_set(v___x_3420_, 0, v___x_3432_);
                    v___x_3438_ = v___x_3420_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3432_);
                    v___x_3438_ = v_reuseFailAlloc_3439_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3438_;
            }
            8 => {
                if v___y_3444_ == 0 {
                    v___y_3423_ = v_a_3406_;
                    state = 3;
                    continue;
                } else {
                    v___x_3445_ = lean_st_ref_take(v_a_3405_);
                    v_subst_3446_ = lean_ctor_get(v___x_3445_, 0);
                    v_jpParamMask_3447_ = lean_ctor_get(v___x_3445_, 1);
                    v_isSharedCheck_3457_ = (!lean_is_exclusive(v___x_3445_)) as u8;
                    if v_isSharedCheck_3457_ == 0 {
                        v___x_3449_ = v___x_3445_;
                        v_isShared_3450_ = v_isSharedCheck_3457_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_jpParamMask_3447_);
                        lean_inc(v_subst_3446_);
                        lean_dec(v___x_3445_);
                        v___x_3449_ = lean_box(0);
                        v_isShared_3450_ = v_isSharedCheck_3457_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3451_ = lean_box(0);
                lean_inc(v_fvarId_3410_);
                v___x_3452_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_3446_, v_fvarId_3410_, v___x_3451_);
                if v_isShared_3450_ == 0 {
                    lean_ctor_set(v___x_3449_, 0, v___x_3452_);
                    v___x_3454_ = v___x_3449_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3452_);
                    lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_jpParamMask_3447_);
                    v___x_3454_ = v_reuseFailAlloc_3456_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3455_ = lean_st_ref_set(v_a_3405_, v___x_3454_);
                v___y_3423_ = v_a_3406_;
                state = 3;
                continue;
            }
            11 => {
                if v_isShared_3464_ == 0 {
                    v___x_3466_ = v___x_3463_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
                    v___x_3466_ = v_reuseFailAlloc_3467_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(
    mut v_p_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
    mut v_a_3472_: *mut LeanObject,
    mut v_a_3473_: *mut LeanObject,
    mut v_a_3474_: *mut LeanObject,
    mut v_a_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3476_: *mut LeanObject = core::ptr::null_mut();
    v_res_3476_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(
            v_p_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_,
        );
    lean_dec(v_a_3474_);
    lean_dec_ref(v_a_3473_);
    lean_dec(v_a_3472_);
    lean_dec(v_a_3471_);
    return v_res_3476_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(
    mut v_p_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
    mut v_a_3481_: *mut LeanObject,
    mut v_a_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(
            v_p_3477_, v_a_3478_, v_a_3480_, v_a_3481_, v_a_3482_,
        );
    return v___x_3484_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(
    mut v_p_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
    mut v_a_3487_: *mut LeanObject,
    mut v_a_3488_: *mut LeanObject,
    mut v_a_3489_: *mut LeanObject,
    mut v_a_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3492_: *mut LeanObject = core::ptr::null_mut();
    v_res_3492_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(
        v_p_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_,
    );
    lean_dec(v_a_3490_);
    lean_dec_ref(v_a_3489_);
    lean_dec(v_a_3488_);
    lean_dec_ref(v_a_3487_);
    lean_dec(v_a_3486_);
    return v_res_3492_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(
    mut v_00_u03b2_3493_: *mut LeanObject,
    mut v_m_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_b_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    v___x_3497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_3494_, v_a_3495_, v_b_3496_);
    return v___x_3497_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(
    mut v_00_u03b2_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_x_3500_: *mut LeanObject,
) -> u8 {
    let mut v___x_3501_: u8 = 0;
    v___x_3501_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_3499_, v_x_3500_);
    return v___x_3501_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(
    mut v_00_u03b2_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
    mut v_x_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3505_: u8 = 0;
    let mut v_r_3506_: *mut LeanObject = core::ptr::null_mut();
    v_res_3505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_3502_, v_a_3503_, v_x_3504_);
    lean_dec(v_x_3504_);
    lean_dec(v_a_3503_);
    v_r_3506_ = lean_box((v_res_3505_) as usize);
    return v_r_3506_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(
    mut v_00_u03b2_3507_: *mut LeanObject,
    mut v_data_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    v___x_3509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_3508_);
    return v___x_3509_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(
    mut v_00_u03b2_3510_: *mut LeanObject,
    mut v_a_3511_: *mut LeanObject,
    mut v_b_3512_: *mut LeanObject,
    mut v_x_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_3511_, v_b_3512_, v_x_3513_);
    return v___x_3514_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3515_: *mut LeanObject,
    mut v_i_3516_: *mut LeanObject,
    mut v_source_3517_: *mut LeanObject,
    mut v_target_3518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    v___x_3519_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_3516_, v_source_3517_, v_target_3518_);
    return v___x_3519_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3520_: *mut LeanObject,
    mut v_x_3521_: *mut LeanObject,
    mut v_x_3522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    v___x_3523_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3521_, v_x_3522_);
    return v___x_3523_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2()
-> *mut LeanObject {
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    v___x_3527_ = lean_box(0);
    v___x_3528_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1;
    v___x_3529_ = l_Lean_Expr_const___override(v___x_3528_, v___x_3527_);
    return v___x_3529_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3()
-> *mut LeanObject {
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    v___x_3530_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
    v___x_3531_ = lean_box(1);
    v___x_3532_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3532_, 0, v___x_3531_);
    lean_ctor_set(v___x_3532_, 1, v___x_3530_);
    return v___x_3532_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6()
-> *mut LeanObject {
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    v___x_3536_ = lean_box(0);
    v___x_3537_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5;
    v___x_3538_ = l_Lean_Expr_const___override(v___x_3537_, v___x_3536_);
    return v___x_3538_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9()
-> *mut LeanObject {
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    v___x_3542_ = lean_box(0);
    v___x_3543_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8;
    v___x_3544_ = l_Lean_Expr_const___override(v___x_3543_, v___x_3542_);
    return v___x_3544_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10()
-> *mut LeanObject {
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    v___x_3545_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
    v___x_3546_ = lean_box(1);
    v___x_3547_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3547_, 0, v___x_3546_);
    lean_ctor_set(v___x_3547_, 1, v___x_3545_);
    return v___x_3547_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(
    mut v_base_3548_: *mut LeanObject,
    mut v_ctorInfo_3549_: *mut LeanObject,
    mut v_field_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3561_: u8 = 0;
    let mut v_i_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3570_: u8 = 0;
    let mut v_size_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut v_unused_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_field_3550_) {
                0 => {
                    lean_dec(v_base_3548_);
                    v___x_3551_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
                    return v___x_3551_;
                }
                1 => {
                    v_i_3552_ = lean_ctor_get(v_field_3550_, 0);
                    v_type_3553_ = lean_ctor_get(v_field_3550_, 1);
                    v_isSharedCheck_3561_ = (!lean_is_exclusive(v_field_3550_)) as u8;
                    if v_isSharedCheck_3561_ == 0 {
                        v___x_3555_ = v_field_3550_;
                        v_isShared_3556_ = v_isSharedCheck_3561_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_type_3553_);
                        lean_inc(v_i_3552_);
                        lean_dec(v_field_3550_);
                        v___x_3555_ = lean_box(0);
                        v_isShared_3556_ = v_isSharedCheck_3561_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_i_3562_ = lean_ctor_get(v_field_3550_, 0);
                    lean_inc(v_i_3562_);
                    lean_dec_ref_known(v_field_3550_, 1);
                    v___x_3563_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3563_, 0, v_i_3562_);
                    lean_ctor_set(v___x_3563_, 1, v_base_3548_);
                    v___x_3564_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
                    v___x_3565_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3565_, 0, v___x_3563_);
                    lean_ctor_set(v___x_3565_, 1, v___x_3564_);
                    return v___x_3565_;
                }
                3 => {
                    v_offset_3566_ = lean_ctor_get(v_field_3550_, 1);
                    v_type_3567_ = lean_ctor_get(v_field_3550_, 2);
                    v_isSharedCheck_3578_ = (!lean_is_exclusive(v_field_3550_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v_unused_3579_ = lean_ctor_get(v_field_3550_, 0);
                        lean_dec(v_unused_3579_);
                        v___x_3569_ = v_field_3550_;
                        v_isShared_3570_ = v_isSharedCheck_3578_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_type_3567_);
                        lean_inc(v_offset_3566_);
                        lean_dec(v_field_3550_);
                        v___x_3569_ = lean_box(0);
                        v_isShared_3570_ = v_isSharedCheck_3578_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_base_3548_);
                    v___x_3580_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
                    return v___x_3580_;
                }
            },
            1 => {
                if v_isShared_3556_ == 0 {
                    lean_ctor_set_tag(v___x_3555_, 6);
                    lean_ctor_set(v___x_3555_, 1, v_base_3548_);
                    v___x_3558_ = v___x_3555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_i_3552_);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_base_3548_);
                    v___x_3558_ = v_reuseFailAlloc_3560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3559_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3559_, 0, v___x_3558_);
                lean_ctor_set(v___x_3559_, 1, v_type_3553_);
                return v___x_3559_;
            }
            3 => {
                v_size_3571_ = lean_ctor_get(v_ctorInfo_3549_, 2);
                v_usize_3572_ = lean_ctor_get(v_ctorInfo_3549_, 3);
                v___x_3573_ = lean_nat_add(v_size_3571_, v_usize_3572_);
                if v_isShared_3570_ == 0 {
                    lean_ctor_set_tag(v___x_3569_, 8);
                    lean_ctor_set(v___x_3569_, 2, v_base_3548_);
                    lean_ctor_set(v___x_3569_, 0, v___x_3573_);
                    v___x_3575_ = v___x_3569_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = lean_alloc_ctor(8, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3573_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_offset_3566_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_base_3548_);
                    v___x_3575_ = v_reuseFailAlloc_3577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3576_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3576_, 0, v___x_3575_);
                lean_ctor_set(v___x_3576_, 1, v_type_3567_);
                return v___x_3576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(
    mut v_base_3581_: *mut LeanObject,
    mut v_ctorInfo_3582_: *mut LeanObject,
    mut v_field_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3584_: *mut LeanObject = core::ptr::null_mut();
    v_res_3584_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(
        v_base_3581_,
        v_ctorInfo_3582_,
        v_field_3583_,
    );
    lean_dec_ref(v_ctorInfo_3582_);
    return v_res_3584_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(
    mut v_arg_3585_: *mut LeanObject,
    mut v_a_3586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3588_ = lean_st_ref_get(v_a_3586_);
                v_subst_3589_ = lean_ctor_get(v___x_3588_, 0);
                lean_inc_ref(v_subst_3589_);
                lean_dec(v___x_3588_);
                v___x_3590_ = 0;
                v___x_3591_ = 1;
                v___x_3592_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
                        v___x_3590_,
                        v_subst_3589_,
                        v_arg_3585_,
                        v___x_3591_,
                    );
                lean_dec_ref(v_subst_3589_);
                if lean_obj_tag(v___x_3592_) == 1 {
                    v_fvarId_3593_ = lean_ctor_get(v___x_3592_, 0);
                    v_isSharedCheck_3601_ = (!lean_is_exclusive(v___x_3592_)) as u8;
                    if v_isSharedCheck_3601_ == 0 {
                        v___x_3595_ = v___x_3592_;
                        v_isShared_3596_ = v_isSharedCheck_3601_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_3593_);
                        lean_dec(v___x_3592_);
                        v___x_3595_ = lean_box(0);
                        v_isShared_3596_ = v_isSharedCheck_3601_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3592_);
                    v___x_3602_ = lean_box(0);
                    v___x_3603_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3603_, 0, v___x_3602_);
                    return v___x_3603_;
                }
            }
            1 => {
                if v_isShared_3596_ == 0 {
                    v___x_3598_ = v___x_3595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_fvarId_3593_);
                    v___x_3598_ = v_reuseFailAlloc_3600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3599_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3599_, 0, v___x_3598_);
                return v___x_3599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(
    mut v_arg_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3607_: *mut LeanObject = core::ptr::null_mut();
    v_res_3607_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(
            v_arg_3604_,
            v_a_3605_,
        );
    lean_dec(v_a_3605_);
    return v_res_3607_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(
    mut v_arg_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
    mut v_a_3612_: *mut LeanObject,
    mut v_a_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    v___x_3615_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(
            v_arg_3608_,
            v_a_3609_,
        );
    return v___x_3615_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(
    mut v_arg_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
    mut v_a_3618_: *mut LeanObject,
    mut v_a_3619_: *mut LeanObject,
    mut v_a_3620_: *mut LeanObject,
    mut v_a_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3623_: *mut LeanObject = core::ptr::null_mut();
    v_res_3623_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(
        v_arg_3616_,
        v_a_3617_,
        v_a_3618_,
        v_a_3619_,
        v_a_3620_,
        v_a_3621_,
    );
    lean_dec(v_a_3621_);
    lean_dec_ref(v_a_3620_);
    lean_dec(v_a_3619_);
    lean_dec_ref(v_a_3618_);
    lean_dec(v_a_3617_);
    return v_res_3623_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(
    mut v_msg_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    v___x_3625_ = l_Lean_instInhabitedExpr;
    v___x_3626_ = lean_panic_fn_borrowed(v___x_3625_, v_msg_3624_);
    return v___x_3626_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3()
-> *mut LeanObject {
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    v___x_3630_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2;
    v___x_3631_ = lean_unsigned_to_nat(11);
    v___x_3632_ = lean_unsigned_to_nat(83);
    v___x_3633_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1;
    v___x_3634_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_3635_ = l_mkPanicMessageWithDecl(
        v___x_3634_,
        v___x_3633_,
        v___x_3632_,
        v___x_3631_,
        v___x_3630_,
    );
    return v___x_3635_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4()
-> *mut LeanObject {
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    v___x_3636_ = lean_box(0);
    v___x_3637_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1;
    v___x_3638_ = l_Lean_mkConst(v___x_3637_, v___x_3636_);
    return v___x_3638_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(
    mut v_type_3639_: *mut LeanObject,
    mut v_arity_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: u8 = 0;
    let mut v_body_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3644_ = lean_unsigned_to_nat(0);
                v___x_3645_ = lean_nat_dec_eq(v_arity_3640_, v___x_3644_);
                if v___x_3645_ == 0 {
                    match lean_obj_tag(v_type_3639_) {
                        7 => {
                            v_body_3646_ = lean_ctor_get(v_type_3639_, 2);
                            v___x_3647_ = lean_unsigned_to_nat(1);
                            v___x_3648_ = lean_nat_sub(v_arity_3640_, v___x_3647_);
                            lean_dec(v_arity_3640_);
                            v_type_3639_ = v_body_3646_;
                            v_arity_3640_ = v___x_3648_;
                            state = 0;
                            continue;
                        }
                        4 => {
                            lean_dec(v_arity_3640_);
                            v_declName_3650_ = lean_ctor_get(v_type_3639_, 0);
                            if lean_obj_tag(v_declName_3650_) == 1 {
                                v_pre_3651_ = lean_ctor_get(v_declName_3650_, 0);
                                if lean_obj_tag(v_pre_3651_) == 0 {
                                    v_str_3652_ = lean_ctor_get(v_declName_3650_, 1);
                                    v___x_3653_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0;
                                    v___x_3654_ = lean_string_dec_eq(v_str_3652_, v___x_3653_);
                                    if v___x_3654_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3655_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
                                        return v___x_3655_;
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
                        _ => {
                            lean_dec(v_arity_3640_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_arity_3640_);
                    lean_inc_ref(v_type_3639_);
                    return v_type_3639_;
                }
            }
            1 => {
                v___x_3642_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
                v___x_3643_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_3642_);
                return v___x_3643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(
    mut v_type_3656_: *mut LeanObject,
    mut v_arity_3657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3658_: *mut LeanObject = core::ptr::null_mut();
    v_res_3658_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_3656_, v_arity_3657_);
    lean_dec_ref(v_type_3656_);
    return v_res_3658_;
}
pub unsafe fn l_Lean_Compiler_LCNF_lowerResultType(
    mut v_type_3659_: *mut LeanObject,
    mut v_arity_3660_: *mut LeanObject,
    mut v_a_3661_: *mut LeanObject,
    mut v_a_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    v___x_3664_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_3659_, v_arity_3660_);
    v___x_3665_ = l_Lean_Compiler_LCNF_toImpureType(v___x_3664_, v_a_3661_, v_a_3662_);
    return v___x_3665_;
}
pub unsafe fn l_Lean_Compiler_LCNF_lowerResultType___boxed(
    mut v_type_3666_: *mut LeanObject,
    mut v_arity_3667_: *mut LeanObject,
    mut v_a_3668_: *mut LeanObject,
    mut v_a_3669_: *mut LeanObject,
    mut v_a_3670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3671_: *mut LeanObject = core::ptr::null_mut();
    v_res_3671_ =
        l_Lean_Compiler_LCNF_lowerResultType(v_type_3666_, v_arity_3667_, v_a_3668_, v_a_3669_);
    lean_dec(v_a_3669_);
    lean_dec_ref(v_a_3668_);
    lean_dec_ref(v_type_3666_);
    return v_res_3671_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2()
-> *mut LeanObject {
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3675_ = lean_box(0);
    v___x_3676_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1;
    v___x_3677_ = l_Lean_Expr_const___override(v___x_3676_, v___x_3675_);
    return v___x_3677_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5()
-> *mut LeanObject {
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    v___x_3681_ = lean_box(0);
    v___x_3682_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4;
    v___x_3683_ = l_Lean_Expr_const___override(v___x_3682_, v___x_3681_);
    return v___x_3683_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8()
-> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = lean_box(0);
    v___x_3688_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7;
    v___x_3689_ = l_Lean_Expr_const___override(v___x_3688_, v___x_3687_);
    return v___x_3689_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11()
-> *mut LeanObject {
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v___x_3693_ = lean_box(0);
    v___x_3694_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10;
    v___x_3695_ = l_Lean_Expr_const___override(v___x_3694_, v___x_3693_);
    return v___x_3695_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14()
-> *mut LeanObject {
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3699_ = lean_box(0);
    v___x_3700_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13;
    v___x_3701_ = l_Lean_Expr_const___override(v___x_3700_, v___x_3699_);
    return v___x_3701_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17()
-> *mut LeanObject {
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    v___x_3705_ = lean_box(0);
    v___x_3706_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16;
    v___x_3707_ = l_Lean_Expr_const___override(v___x_3706_, v___x_3705_);
    return v___x_3707_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20()
-> *mut LeanObject {
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    v___x_3711_ = lean_box(0);
    v___x_3712_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19;
    v___x_3713_ = l_Lean_Expr_const___override(v___x_3712_, v___x_3711_);
    return v___x_3713_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(
    mut v_v_3714_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_v_3714_) {
        0 => {
            let mut v_val_3715_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3717_: u8 = 0;
            v_val_3715_ = lean_ctor_get(v_v_3714_, 0);
            v___x_3716_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
            v___x_3717_ = lean_nat_dec_lt(v_val_3715_, v___x_3716_);
            if v___x_3717_ == 0 {
                let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
                v___x_3718_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
                return v___x_3718_;
            } else {
                let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
                v___x_3719_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
                return v___x_3719_;
            }
        }
        1 => {
            let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
            v___x_3720_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
            return v___x_3720_;
        }
        2 => {
            let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
            v___x_3721_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
            return v___x_3721_;
        }
        3 => {
            let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
            v___x_3722_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
            return v___x_3722_;
        }
        4 => {
            let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
            v___x_3723_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
            return v___x_3723_;
        }
        5 => {
            let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
            v___x_3724_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20);
            return v___x_3724_;
        }
        _ => {
            let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
            v___x_3725_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
            return v___x_3725_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(
    mut v_v_3726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3727_: *mut LeanObject = core::ptr::null_mut();
    v_res_3727_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_3726_);
    lean_dec_ref(v_v_3726_);
    return v_res_3727_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(
    mut v_as_3728_: *mut LeanObject,
    mut v_i_3729_: usize,
    mut v_stop_3730_: usize,
    mut v_b_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: usize = 0;
    let mut v___x_3735_: usize = 0;
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    let mut v_fst_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3737_ = lean_usize_dec_eq(v_i_3729_, v_stop_3730_);
                if v___x_3737_ == 0 {
                    v___x_3738_ = lean_array_uget_borrowed(v_as_3728_, v_i_3729_);
                    v_snd_3739_ = lean_ctor_get(v___x_3738_, 1);
                    v___x_3740_ = (lean_unbox(v_snd_3739_) as u8);
                    if v___x_3740_ == 0 {
                        v___y_3733_ = v_b_3731_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_3741_ = lean_ctor_get(v___x_3738_, 0);
                        lean_inc(v_fst_3741_);
                        v___x_3742_ = lean_array_push(v_b_3731_, v_fst_3741_);
                        v___y_3733_ = v___x_3742_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3731_;
                }
            }
            1 => {
                v___x_3734_ = 1usize;
                v___x_3735_ = lean_usize_add(v_i_3729_, v___x_3734_);
                v_i_3729_ = v___x_3735_;
                v_b_3731_ = v___y_3733_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(
    mut v_as_3743_: *mut LeanObject,
    mut v_i_3744_: *mut LeanObject,
    mut v_stop_3745_: *mut LeanObject,
    mut v_b_3746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3747_: usize = 0;
    let mut v_stop_boxed_3748_: usize = 0;
    let mut v_res_3749_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3747_ = lean_unbox_usize(v_i_3744_);
    lean_dec(v_i_3744_);
    v_stop_boxed_3748_ = lean_unbox_usize(v_stop_3745_);
    lean_dec(v_stop_3745_);
    v_res_3749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_3743_, v_i_boxed_3747_, v_stop_boxed_3748_, v_b_3746_);
    lean_dec_ref(v_as_3743_);
    return v_res_3749_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    v___x_3750_ = 1;
    v___x_3751_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_3750_);
    return v___x_3751_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(
    mut v_msg_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v_toFunctor_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3786_: u8 = 0;
    let mut v___f_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37650__overap_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3806_: u8 = 0;
    let mut v_unused_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3808_: u8 = 0;
    let mut v_unused_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3759_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
                v_toApplicative_3760_ = lean_ctor_get(v___x_3759_, 0);
                v_toFunctor_3761_ = lean_ctor_get(v_toApplicative_3760_, 0);
                v_toSeq_3762_ = lean_ctor_get(v_toApplicative_3760_, 2);
                v_toSeqLeft_3763_ = lean_ctor_get(v_toApplicative_3760_, 3);
                v_toSeqRight_3764_ = lean_ctor_get(v_toApplicative_3760_, 4);
                v___f_3765_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2;
                v___f_3766_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3;
                lean_inc_ref_n(v_toFunctor_3761_, 2);
                v___f_3767_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3767_, 0, v_toFunctor_3761_);
                v___f_3768_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3768_, 0, v_toFunctor_3761_);
                v___x_3769_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3769_, 0, v___f_3767_);
                lean_ctor_set(v___x_3769_, 1, v___f_3768_);
                lean_inc(v_toSeqRight_3764_);
                v___f_3770_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3770_, 0, v_toSeqRight_3764_);
                lean_inc(v_toSeqLeft_3763_);
                v___f_3771_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3771_, 0, v_toSeqLeft_3763_);
                lean_inc(v_toSeq_3762_);
                v___f_3772_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3772_, 0, v_toSeq_3762_);
                v___x_3773_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3773_, 0, v___x_3769_);
                lean_ctor_set(v___x_3773_, 1, v___f_3765_);
                lean_ctor_set(v___x_3773_, 2, v___f_3772_);
                lean_ctor_set(v___x_3773_, 3, v___f_3771_);
                lean_ctor_set(v___x_3773_, 4, v___f_3770_);
                v___x_3774_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3774_, 0, v___x_3773_);
                lean_ctor_set(v___x_3774_, 1, v___f_3766_);
                v___x_3775_ = l_StateRefT_x27_instMonad___redArg(v___x_3774_);
                v_toApplicative_3776_ = lean_ctor_get(v___x_3775_, 0);
                v_isSharedCheck_3808_ = (!lean_is_exclusive(v___x_3775_)) as u8;
                if v_isSharedCheck_3808_ == 0 {
                    v_unused_3809_ = lean_ctor_get(v___x_3775_, 1);
                    lean_dec(v_unused_3809_);
                    v___x_3778_ = v___x_3775_;
                    v_isShared_3779_ = v_isSharedCheck_3808_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3776_);
                    lean_dec(v___x_3775_);
                    v___x_3778_ = lean_box(0);
                    v_isShared_3779_ = v_isSharedCheck_3808_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3780_ = lean_ctor_get(v_toApplicative_3776_, 0);
                v_toSeq_3781_ = lean_ctor_get(v_toApplicative_3776_, 2);
                v_toSeqLeft_3782_ = lean_ctor_get(v_toApplicative_3776_, 3);
                v_toSeqRight_3783_ = lean_ctor_get(v_toApplicative_3776_, 4);
                v_isSharedCheck_3806_ = (!lean_is_exclusive(v_toApplicative_3776_)) as u8;
                if v_isSharedCheck_3806_ == 0 {
                    v_unused_3807_ = lean_ctor_get(v_toApplicative_3776_, 1);
                    lean_dec(v_unused_3807_);
                    v___x_3785_ = v_toApplicative_3776_;
                    v_isShared_3786_ = v_isSharedCheck_3806_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3783_);
                    lean_inc(v_toSeqLeft_3782_);
                    lean_inc(v_toSeq_3781_);
                    lean_inc(v_toFunctor_3780_);
                    lean_dec(v_toApplicative_3776_);
                    v___x_3785_ = lean_box(0);
                    v_isShared_3786_ = v_isSharedCheck_3806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3787_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5;
                v___f_3788_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6;
                lean_inc_ref(v_toFunctor_3780_);
                v___f_3789_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3789_, 0, v_toFunctor_3780_);
                v___f_3790_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3790_, 0, v_toFunctor_3780_);
                v___x_3791_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3791_, 0, v___f_3789_);
                lean_ctor_set(v___x_3791_, 1, v___f_3790_);
                v___f_3792_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3792_, 0, v_toSeqRight_3783_);
                v___f_3793_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3793_, 0, v_toSeqLeft_3782_);
                v___f_3794_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3794_, 0, v_toSeq_3781_);
                if v_isShared_3786_ == 0 {
                    lean_ctor_set(v___x_3785_, 4, v___f_3792_);
                    lean_ctor_set(v___x_3785_, 3, v___f_3793_);
                    lean_ctor_set(v___x_3785_, 2, v___f_3794_);
                    lean_ctor_set(v___x_3785_, 1, v___f_3787_);
                    lean_ctor_set(v___x_3785_, 0, v___x_3791_);
                    v___x_3796_ = v___x_3785_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3791_);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 1, v___f_3787_);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 2, v___f_3794_);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 3, v___f_3793_);
                    lean_ctor_set(v_reuseFailAlloc_3805_, 4, v___f_3792_);
                    v___x_3796_ = v_reuseFailAlloc_3805_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3779_ == 0 {
                    lean_ctor_set(v___x_3778_, 1, v___f_3788_);
                    lean_ctor_set(v___x_3778_, 0, v___x_3796_);
                    v___x_3798_ = v___x_3778_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3796_);
                    lean_ctor_set(v_reuseFailAlloc_3804_, 1, v___f_3788_);
                    v___x_3798_ = v_reuseFailAlloc_3804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3799_ = l_StateRefT_x27_instMonad___redArg(v___x_3798_);
                v___x_3800_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
                v___x_3801_ = l_instInhabitedOfMonad___redArg(v___x_3799_, v___x_3800_);
                v___x_37650__overap_3802_ = lean_panic_fn_borrowed(v___x_3801_, v_msg_3752_);
                lean_dec(v___x_3801_);
                lean_inc(v___y_3757_);
                lean_inc_ref(v___y_3756_);
                lean_inc(v___y_3755_);
                lean_inc_ref(v___y_3754_);
                lean_inc(v___y_3753_);
                v___x_3803_ = lean_apply_6(
                    v___x_37650__overap_3802_,
                    v___y_3753_,
                    v___y_3754_,
                    v___y_3755_,
                    v___y_3756_,
                    v___y_3757_,
                    lean_box(0),
                );
                return v___x_3803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(
    mut v_msg_3810_: *mut LeanObject,
    mut v___y_3811_: *mut LeanObject,
    mut v___y_3812_: *mut LeanObject,
    mut v___y_3813_: *mut LeanObject,
    mut v___y_3814_: *mut LeanObject,
    mut v___y_3815_: *mut LeanObject,
    mut v___y_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3817_: *mut LeanObject = core::ptr::null_mut();
    v_res_3817_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
    lean_dec(v___y_3815_);
    lean_dec_ref(v___y_3814_);
    lean_dec(v___y_3813_);
    lean_dec_ref(v___y_3812_);
    lean_dec(v___y_3811_);
    return v_res_3817_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v___x_3818_ = 0;
    v___x_3819_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_3818_);
    return v___x_3819_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(
    mut v_upperBound_3820_: *mut LeanObject,
    mut v_params_3821_: *mut LeanObject,
    mut v___x_3822_: *mut LeanObject,
    mut v_discr_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
    mut v_b_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: u8 = 0;
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3833_ = lean_nat_dec_lt(v_a_3824_, v_upperBound_3820_);
                if v___x_3833_ == 0 {
                    lean_dec(v_a_3824_);
                    lean_dec(v_discr_3823_);
                    v___x_3834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3834_, 0, v_b_3825_);
                    return v___x_3834_;
                } else {
                    v___x_3835_ = lean_box(0);
                    v___x_3836_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
                    v___x_3837_ = lean_array_get_borrowed(v___x_3836_, v_params_3821_, v_a_3824_);
                    v___x_3838_ = lean_nat_dec_eq(v_a_3824_, v___x_3822_);
                    if v___x_3838_ == 0 {
                        v___x_3839_ = lean_st_ref_take(v___y_3826_);
                        v_fvarId_3840_ = lean_ctor_get(v___x_3837_, 0);
                        v_subst_3841_ = lean_ctor_get(v___x_3839_, 0);
                        v_jpParamMask_3842_ = lean_ctor_get(v___x_3839_, 1);
                        v_isSharedCheck_3852_ = (!lean_is_exclusive(v___x_3839_)) as u8;
                        if v_isSharedCheck_3852_ == 0 {
                            v___x_3844_ = v___x_3839_;
                            v_isShared_3845_ = v_isSharedCheck_3852_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_jpParamMask_3842_);
                            lean_inc(v_subst_3841_);
                            lean_dec(v___x_3839_);
                            v___x_3844_ = lean_box(0);
                            v_isShared_3845_ = v_isSharedCheck_3852_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3853_ = lean_st_ref_take(v___y_3826_);
                        v_fvarId_3854_ = lean_ctor_get(v___x_3837_, 0);
                        v_subst_3855_ = lean_ctor_get(v___x_3853_, 0);
                        v_jpParamMask_3856_ = lean_ctor_get(v___x_3853_, 1);
                        v_isSharedCheck_3866_ = (!lean_is_exclusive(v___x_3853_)) as u8;
                        if v_isSharedCheck_3866_ == 0 {
                            v___x_3858_ = v___x_3853_;
                            v_isShared_3859_ = v_isSharedCheck_3866_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_jpParamMask_3856_);
                            lean_inc(v_subst_3855_);
                            lean_dec(v___x_3853_);
                            v___x_3858_ = lean_box(0);
                            v_isShared_3859_ = v_isSharedCheck_3866_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3830_ = lean_unsigned_to_nat(1);
                v___x_3831_ = lean_nat_add(v_a_3824_, v___x_3830_);
                lean_dec(v_a_3824_);
                v_a_3824_ = v___x_3831_;
                v_b_3825_ = v_a_3829_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3846_ = lean_box(0);
                lean_inc(v_fvarId_3840_);
                v___x_3847_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_3841_, v_fvarId_3840_, v___x_3846_);
                if v_isShared_3845_ == 0 {
                    lean_ctor_set(v___x_3844_, 0, v___x_3847_);
                    v___x_3849_ = v___x_3844_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3847_);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_jpParamMask_3842_);
                    v___x_3849_ = v_reuseFailAlloc_3851_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3850_ = lean_st_ref_set(v___y_3826_, v___x_3849_);
                v_a_3829_ = v___x_3835_;
                state = 1;
                continue;
            }
            4 => {
                lean_inc(v_discr_3823_);
                v___x_3860_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3860_, 0, v_discr_3823_);
                lean_inc(v_fvarId_3854_);
                v___x_3861_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_3855_, v_fvarId_3854_, v___x_3860_);
                if v_isShared_3859_ == 0 {
                    lean_ctor_set(v___x_3858_, 0, v___x_3861_);
                    v___x_3863_ = v___x_3858_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3861_);
                    lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_jpParamMask_3856_);
                    v___x_3863_ = v_reuseFailAlloc_3865_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3864_ = lean_st_ref_set(v___y_3826_, v___x_3863_);
                v_a_3829_ = v___x_3835_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(
    mut v_upperBound_3867_: *mut LeanObject,
    mut v_params_3868_: *mut LeanObject,
    mut v___x_3869_: *mut LeanObject,
    mut v_discr_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_b_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_res_3875_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_3867_, v_params_3868_, v___x_3869_, v_discr_3870_, v_a_3871_, v_b_3872_, v___y_3873_);
    lean_dec(v___y_3873_);
    lean_dec(v___x_3869_);
    lean_dec_ref(v_params_3868_);
    lean_dec(v_upperBound_3867_);
    return v_res_3875_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(
    mut v_sz_3876_: usize,
    mut v_i_3877_: usize,
    mut v_bs_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3879_: u8 = 0;
    let mut v_v_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: u8 = 0;
    let mut v___x_3886_: usize = 0;
    let mut v___x_3887_: usize = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: u8 = 0;
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3894_: u8 = 0;
    let mut v___x_3895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3879_ = lean_usize_dec_lt(v_i_3877_, v_sz_3876_);
                if v___x_3879_ == 0 {
                    return v_bs_3878_;
                } else {
                    v_v_3880_ = lean_array_uget_borrowed(v_bs_3878_, v_i_3877_);
                    v_type_3881_ = lean_ctor_get(v_v_3880_, 2);
                    lean_inc_ref(v_type_3881_);
                    v___x_3882_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3883_ = lean_array_uset(v_bs_3878_, v_i_3877_, v___x_3882_);
                    v___x_3894_ = l_Lean_Expr_isVoid(v_type_3881_);
                    if v___x_3894_ == 0 {
                        v___x_3895_ = l_Lean_Expr_isErased(v_type_3881_);
                        lean_dec_ref(v_type_3881_);
                        v___y_3892_ = v___x_3895_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_type_3881_);
                        v___y_3892_ = v___x_3894_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3886_ = 1usize;
                v___x_3887_ = lean_usize_add(v_i_3877_, v___x_3886_);
                v___x_3888_ = lean_box((v___y_3885_) as usize);
                v___x_3889_ = lean_array_uset(v_bs_x27_3883_, v_i_3877_, v___x_3888_);
                v_i_3877_ = v___x_3887_;
                v_bs_3878_ = v___x_3889_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3892_ == 0 {
                    v___y_3885_ = v___x_3879_;
                    state = 1;
                    continue;
                } else {
                    v___x_3893_ = 0;
                    v___y_3885_ = v___x_3893_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(
    mut v_sz_3896_: *mut LeanObject,
    mut v_i_3897_: *mut LeanObject,
    mut v_bs_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3899_: usize = 0;
    let mut v_i_boxed_3900_: usize = 0;
    let mut v_res_3901_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3899_ = lean_unbox_usize(v_sz_3896_);
    lean_dec(v_sz_3896_);
    v_i_boxed_3900_ = lean_unbox_usize(v_i_3897_);
    lean_dec(v_i_3897_);
    v_res_3901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_3899_, v_i_boxed_3900_, v_bs_3898_);
    return v_res_3901_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    v___x_3902_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3902_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    v___x_3903_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
    v___x_3904_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3904_, 0, v___x_3903_);
    return v___x_3904_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    v___x_3905_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
    v___x_3906_ = lean_unsigned_to_nat(0);
    v___x_3907_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3907_, 0, v___x_3906_);
    lean_ctor_set(v___x_3907_, 1, v___x_3906_);
    lean_ctor_set(v___x_3907_, 2, v___x_3906_);
    lean_ctor_set(v___x_3907_, 3, v___x_3906_);
    lean_ctor_set(v___x_3907_, 4, v___x_3905_);
    lean_ctor_set(v___x_3907_, 5, v___x_3905_);
    lean_ctor_set(v___x_3907_, 6, v___x_3905_);
    lean_ctor_set(v___x_3907_, 7, v___x_3905_);
    lean_ctor_set(v___x_3907_, 8, v___x_3905_);
    lean_ctor_set(v___x_3907_, 9, v___x_3905_);
    return v___x_3907_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(
    mut v_msg_3908_: *mut LeanObject,
    mut v___y_3909_: *mut LeanObject,
    mut v___y_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v_env_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3939_: u8 = 0;
    let mut v_unused_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3941_: u8 = 0;
    let mut v_a_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3914_ = lean_ctor_get(v___y_3911_, 2);
                v_ref_3915_ = lean_ctor_get(v___y_3911_, 5);
                v___x_3916_ = lean_st_ref_get(v___y_3912_);
                v___x_3917_ = lean_st_ref_get(v___y_3910_);
                v___x_3918_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3909_);
                if lean_obj_tag(v___x_3918_) == 0 {
                    v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
                    v_isSharedCheck_3941_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                    if v_isSharedCheck_3941_ == 0 {
                        v___x_3921_ = v___x_3918_;
                        v_isShared_3922_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3919_);
                        lean_dec(v___x_3918_);
                        v___x_3921_ = lean_box(0);
                        v_isShared_3922_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3917_);
                    lean_dec(v___x_3916_);
                    lean_dec_ref(v_msg_3908_);
                    v_a_3942_ = lean_ctor_get(v___x_3918_, 0);
                    v_isSharedCheck_3949_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                    if v_isSharedCheck_3949_ == 0 {
                        v___x_3944_ = v___x_3918_;
                        v_isShared_3945_ = v_isSharedCheck_3949_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3942_);
                        lean_dec(v___x_3918_);
                        v___x_3944_ = lean_box(0);
                        v_isShared_3945_ = v_isSharedCheck_3949_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3923_ = lean_ctor_get(v___x_3916_, 0);
                lean_inc_ref(v_env_3923_);
                lean_dec(v___x_3916_);
                v_lctx_3924_ = lean_ctor_get(v___x_3917_, 0);
                v_isSharedCheck_3939_ = (!lean_is_exclusive(v___x_3917_)) as u8;
                if v_isSharedCheck_3939_ == 0 {
                    v_unused_3940_ = lean_ctor_get(v___x_3917_, 1);
                    lean_dec(v_unused_3940_);
                    v___x_3926_ = v___x_3917_;
                    v_isShared_3927_ = v_isSharedCheck_3939_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_3924_);
                    lean_dec(v___x_3917_);
                    v___x_3926_ = lean_box(0);
                    v_isShared_3927_ = v_isSharedCheck_3939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3928_ = (lean_unbox(v_a_3919_) as u8);
                lean_dec(v_a_3919_);
                v___x_3929_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3924_, v___x_3928_);
                lean_dec_ref(v_lctx_3924_);
                v___x_3930_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
                lean_inc_ref(v_options_3914_);
                v___x_3931_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3931_, 0, v_env_3923_);
                lean_ctor_set(v___x_3931_, 1, v___x_3930_);
                lean_ctor_set(v___x_3931_, 2, v___x_3929_);
                lean_ctor_set(v___x_3931_, 3, v_options_3914_);
                if v_isShared_3927_ == 0 {
                    lean_ctor_set_tag(v___x_3926_, 3);
                    lean_ctor_set(v___x_3926_, 1, v_msg_3908_);
                    lean_ctor_set(v___x_3926_, 0, v___x_3931_);
                    v___x_3933_ = v___x_3926_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3938_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3931_);
                    lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_msg_3908_);
                    v___x_3933_ = v_reuseFailAlloc_3938_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_ref_3915_);
                v___x_3934_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3934_, 0, v_ref_3915_);
                lean_ctor_set(v___x_3934_, 1, v___x_3933_);
                if v_isShared_3922_ == 0 {
                    lean_ctor_set_tag(v___x_3921_, 1);
                    lean_ctor_set(v___x_3921_, 0, v___x_3934_);
                    v___x_3936_ = v___x_3921_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
                    v___x_3936_ = v_reuseFailAlloc_3937_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3936_;
            }
            5 => {
                if v_isShared_3945_ == 0 {
                    v___x_3947_ = v___x_3944_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
                    v___x_3947_ = v_reuseFailAlloc_3948_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(
    mut v_msg_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
    lean_dec(v___y_3954_);
    lean_dec_ref(v___y_3953_);
    lean_dec(v___y_3952_);
    lean_dec_ref(v___y_3951_);
    return v_res_3956_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(
    mut v_sz_3957_: usize,
    mut v_i_3958_: usize,
    mut v_bs_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: usize = 0;
    let mut v___x_3970_: usize = 0;
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3976_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3962_ = lean_usize_dec_lt(v_i_3958_, v_sz_3957_);
                if v___x_3962_ == 0 {
                    v___x_3963_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3963_, 0, v_bs_3959_);
                    return v___x_3963_;
                } else {
                    v_v_3964_ = lean_array_uget_borrowed(v_bs_3959_, v_i_3958_);
                    lean_inc(v_v_3964_);
                    v___x_3965_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_3964_, v___y_3960_);
                    if lean_obj_tag(v___x_3965_) == 0 {
                        v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
                        lean_inc(v_a_3966_);
                        lean_dec_ref_known(v___x_3965_, 1);
                        v___x_3967_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3968_ = lean_array_uset(v_bs_3959_, v_i_3958_, v___x_3967_);
                        v___x_3969_ = 1usize;
                        v___x_3970_ = lean_usize_add(v_i_3958_, v___x_3969_);
                        v___x_3971_ = lean_array_uset(v_bs_x27_3968_, v_i_3958_, v_a_3966_);
                        v_i_3958_ = v___x_3970_;
                        v_bs_3959_ = v___x_3971_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3959_);
                        v_a_3973_ = lean_ctor_get(v___x_3965_, 0);
                        v_isSharedCheck_3980_ = (!lean_is_exclusive(v___x_3965_)) as u8;
                        if v_isSharedCheck_3980_ == 0 {
                            v___x_3975_ = v___x_3965_;
                            v_isShared_3976_ = v_isSharedCheck_3980_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3973_);
                            lean_dec(v___x_3965_);
                            v___x_3975_ = lean_box(0);
                            v_isShared_3976_ = v_isSharedCheck_3980_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3976_ == 0 {
                    v___x_3978_ = v___x_3975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
                    v___x_3978_ = v_reuseFailAlloc_3979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(
    mut v_sz_3981_: *mut LeanObject,
    mut v_i_3982_: *mut LeanObject,
    mut v_bs_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3986_: usize = 0;
    let mut v_i_boxed_3987_: usize = 0;
    let mut v_res_3988_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3986_ = lean_unbox_usize(v_sz_3981_);
    lean_dec(v_sz_3981_);
    v_i_boxed_3987_ = lean_unbox_usize(v_i_3982_);
    lean_dec(v_i_3982_);
    v_res_3988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_3986_, v_i_boxed_3987_, v_bs_3983_, v___y_3984_);
    lean_dec(v___y_3984_);
    return v_res_3988_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(
    mut v_upperBound_3989_: *mut LeanObject,
    mut v_fieldInfo_3990_: *mut LeanObject,
    mut v___x_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
    mut v_b_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: u8 = 0;
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4000_ = lean_nat_dec_lt(v_a_3992_, v_upperBound_3989_);
                if v___x_4000_ == 0 {
                    lean_dec(v_a_3992_);
                    v___x_4001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4001_, 0, v_b_3993_);
                    return v___x_4001_;
                } else {
                    v___x_4002_ = lean_array_fget_borrowed(v_fieldInfo_3990_, v_a_3992_);
                    match lean_obj_tag(v___x_4002_) {
                        1 => {
                            v___x_4003_ = lean_box(0);
                            v___x_4004_ =
                                lean_array_get_borrowed(v___x_4003_, v___x_3991_, v_a_3992_);
                            lean_inc(v___x_4004_);
                            v___x_4005_ = lean_array_push(v_b_3993_, v___x_4004_);
                            v_a_3996_ = v___x_4005_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_a_3996_ = v_b_3993_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            v_a_3996_ = v_b_3993_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_a_3996_ = v_b_3993_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3997_ = lean_unsigned_to_nat(1);
                v___x_3998_ = lean_nat_add(v_a_3992_, v___x_3997_);
                lean_dec(v_a_3992_);
                v_a_3992_ = v___x_3998_;
                v_b_3993_ = v_a_3996_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(
    mut v_upperBound_4006_: *mut LeanObject,
    mut v_fieldInfo_4007_: *mut LeanObject,
    mut v___x_4008_: *mut LeanObject,
    mut v_a_4009_: *mut LeanObject,
    mut v_b_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4012_: *mut LeanObject = core::ptr::null_mut();
    v_res_4012_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_4006_, v_fieldInfo_4007_, v___x_4008_, v_a_4009_, v_b_4010_);
    lean_dec_ref(v___x_4008_);
    lean_dec_ref(v_fieldInfo_4007_);
    lean_dec(v_upperBound_4006_);
    return v_res_4012_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(
    mut v_as_4013_: *mut LeanObject,
    mut v_i_4014_: usize,
    mut v_stop_4015_: usize,
    mut v_b_4016_: *mut LeanObject,
    mut v___y_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: usize = 0;
    let mut v___x_4022_: usize = 0;
    let mut v___x_4024_: u8 = 0;
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: u8 = 0;
    let mut v_fst_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4039_: u8 = 0;
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4024_ = lean_usize_dec_eq(v_i_4014_, v_stop_4015_);
                if v___x_4024_ == 0 {
                    v___x_4025_ = lean_array_uget_borrowed(v_as_4013_, v_i_4014_);
                    v_snd_4026_ = lean_ctor_get(v___x_4025_, 1);
                    v___x_4027_ = (lean_unbox(v_snd_4026_) as u8);
                    if v___x_4027_ == 0 {
                        v_a_4020_ = v_b_4016_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_4028_ = lean_ctor_get(v___x_4025_, 0);
                        lean_inc(v_fst_4028_);
                        v___x_4029_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_4028_, v___y_4017_);
                        if lean_obj_tag(v___x_4029_) == 0 {
                            v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
                            lean_inc(v_a_4030_);
                            lean_dec_ref_known(v___x_4029_, 1);
                            v___x_4031_ = lean_array_push(v_b_4016_, v_a_4030_);
                            v_a_4020_ = v___x_4031_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_4016_);
                            v_a_4032_ = lean_ctor_get(v___x_4029_, 0);
                            v_isSharedCheck_4039_ = (!lean_is_exclusive(v___x_4029_)) as u8;
                            if v_isSharedCheck_4039_ == 0 {
                                v___x_4034_ = v___x_4029_;
                                v_isShared_4035_ = v_isSharedCheck_4039_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4032_);
                                lean_dec(v___x_4029_);
                                v___x_4034_ = lean_box(0);
                                v_isShared_4035_ = v_isSharedCheck_4039_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_4040_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4040_, 0, v_b_4016_);
                    return v___x_4040_;
                }
            }
            1 => {
                v___x_4021_ = 1usize;
                v___x_4022_ = lean_usize_add(v_i_4014_, v___x_4021_);
                v_i_4014_ = v___x_4022_;
                v_b_4016_ = v_a_4020_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4035_ == 0 {
                    v___x_4037_ = v___x_4034_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
                    v___x_4037_ = v_reuseFailAlloc_4038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(
    mut v_as_4041_: *mut LeanObject,
    mut v_i_4042_: *mut LeanObject,
    mut v_stop_4043_: *mut LeanObject,
    mut v_b_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4047_: usize = 0;
    let mut v_stop_boxed_4048_: usize = 0;
    let mut v_res_4049_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4047_ = lean_unbox_usize(v_i_4042_);
    lean_dec(v_i_4042_);
    v_stop_boxed_4048_ = lean_unbox_usize(v_stop_4043_);
    lean_dec(v_stop_4043_);
    v_res_4049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_4041_, v_i_boxed_4047_, v_stop_boxed_4048_, v_b_4044_, v___y_4045_);
    lean_dec(v___y_4045_);
    lean_dec_ref(v_as_4041_);
    return v_res_4049_;
}
pub unsafe fn _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0()
-> *mut LeanObject {
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Array_instInhabited(lean_box(0));
    return v___x_4050_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(
    mut v_msg_4051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    v___x_4052_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once), _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0);
    v___x_4053_ = lean_panic_fn_borrowed(v___x_4052_, v_msg_4051_);
    return v___x_4053_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3()
-> *mut LeanObject {
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2;
    v___x_4058_ = lean_unsigned_to_nat(11);
    v___x_4059_ = lean_unsigned_to_nat(163);
    v___x_4060_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1;
    v___x_4061_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0;
    v___x_4062_ = l_mkPanicMessageWithDecl(
        v___x_4061_,
        v___x_4060_,
        v___x_4059_,
        v___x_4058_,
        v___x_4057_,
    );
    return v___x_4062_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(
    mut v_a_4063_: *mut LeanObject,
    mut v_x_4064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4064_) == 0 {
                    v___x_4065_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3);
                    v___x_4066_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(v___x_4065_);
                    return v___x_4066_;
                } else {
                    v_key_4067_ = lean_ctor_get(v_x_4064_, 0);
                    v_value_4068_ = lean_ctor_get(v_x_4064_, 1);
                    v_tail_4069_ = lean_ctor_get(v_x_4064_, 2);
                    v___x_4070_ = l_Lean_instBEqFVarId_beq(v_key_4067_, v_a_4063_);
                    if v___x_4070_ == 0 {
                        v_x_4064_ = v_tail_4069_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4068_);
                        return v_value_4068_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(
    mut v_a_4072_: *mut LeanObject,
    mut v_x_4073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4074_: *mut LeanObject = core::ptr::null_mut();
    v_res_4074_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_4072_, v_x_4073_);
    lean_dec(v_x_4073_);
    lean_dec(v_a_4072_);
    return v_res_4074_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(
    mut v_m_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: u64 = 0;
    let mut v___x_4080_: u64 = 0;
    let mut v___x_4081_: u64 = 0;
    let mut v_fold_4082_: u64 = 0;
    let mut v___x_4083_: u64 = 0;
    let mut v___x_4084_: u64 = 0;
    let mut v___x_4085_: u64 = 0;
    let mut v___x_4086_: usize = 0;
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: usize = 0;
    let mut v___x_4089_: usize = 0;
    let mut v___x_4090_: usize = 0;
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_4077_ = lean_ctor_get(v_m_4075_, 1);
    v___x_4078_ = lean_array_get_size(v_buckets_4077_);
    v___x_4079_ = l_Lean_instHashableFVarId_hash(v_a_4076_);
    v___x_4080_ = 32u64;
    v___x_4081_ = lean_uint64_shift_right(v___x_4079_, v___x_4080_);
    v_fold_4082_ = lean_uint64_xor(v___x_4079_, v___x_4081_);
    v___x_4083_ = 16u64;
    v___x_4084_ = lean_uint64_shift_right(v_fold_4082_, v___x_4083_);
    v___x_4085_ = lean_uint64_xor(v_fold_4082_, v___x_4084_);
    v___x_4086_ = lean_uint64_to_usize(v___x_4085_);
    v___x_4087_ = lean_usize_of_nat(v___x_4078_);
    v___x_4088_ = 1usize;
    v___x_4089_ = lean_usize_sub(v___x_4087_, v___x_4088_);
    v___x_4090_ = lean_usize_land(v___x_4086_, v___x_4089_);
    v___x_4091_ = lean_array_uget_borrowed(v_buckets_4077_, v___x_4090_);
    v___x_4092_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_4076_, v___x_4091_);
    return v___x_4092_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(
    mut v_m_4093_: *mut LeanObject,
    mut v_a_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4095_: *mut LeanObject = core::ptr::null_mut();
    v_res_4095_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_4093_, v_a_4094_);
    lean_dec(v_a_4094_);
    lean_dec_ref(v_m_4093_);
    return v_res_4095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(
    mut v_sz_4096_: usize,
    mut v_i_4097_: usize,
    mut v_bs_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: usize = 0;
    let mut v___x_4112_: usize = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4104_ = lean_usize_dec_lt(v_i_4097_, v_sz_4096_);
                if v___x_4104_ == 0 {
                    v___x_4105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4105_, 0, v_bs_4098_);
                    return v___x_4105_;
                } else {
                    v_v_4106_ = lean_array_uget_borrowed(v_bs_4098_, v_i_4097_);
                    lean_inc(v_v_4106_);
                    v___x_4107_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_4106_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
                    if lean_obj_tag(v___x_4107_) == 0 {
                        v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
                        lean_inc(v_a_4108_);
                        lean_dec_ref_known(v___x_4107_, 1);
                        v___x_4109_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4110_ = lean_array_uset(v_bs_4098_, v_i_4097_, v___x_4109_);
                        v___x_4111_ = 1usize;
                        v___x_4112_ = lean_usize_add(v_i_4097_, v___x_4111_);
                        v___x_4113_ = lean_array_uset(v_bs_x27_4110_, v_i_4097_, v_a_4108_);
                        v_i_4097_ = v___x_4112_;
                        v_bs_4098_ = v___x_4113_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_4098_);
                        v_a_4115_ = lean_ctor_get(v___x_4107_, 0);
                        v_isSharedCheck_4122_ = (!lean_is_exclusive(v___x_4107_)) as u8;
                        if v_isSharedCheck_4122_ == 0 {
                            v___x_4117_ = v___x_4107_;
                            v_isShared_4118_ = v_isSharedCheck_4122_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4115_);
                            lean_dec(v___x_4107_);
                            v___x_4117_ = lean_box(0);
                            v_isShared_4118_ = v_isSharedCheck_4122_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4118_ == 0 {
                    v___x_4120_ = v___x_4117_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
                    v___x_4120_ = v_reuseFailAlloc_4121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(
    mut v_sz_4123_: *mut LeanObject,
    mut v_i_4124_: *mut LeanObject,
    mut v_bs_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4131_: usize = 0;
    let mut v_i_boxed_4132_: usize = 0;
    let mut v_res_4133_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4131_ = lean_unbox_usize(v_sz_4123_);
    lean_dec(v_sz_4123_);
    v_i_boxed_4132_ = lean_unbox_usize(v_i_4124_);
    lean_dec(v_i_4124_);
    v_res_4133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_4131_, v_i_boxed_4132_, v_bs_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
    lean_dec(v___y_4129_);
    lean_dec_ref(v___y_4128_);
    lean_dec(v___y_4127_);
    lean_dec(v___y_4126_);
    return v_res_4133_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2()
-> *mut LeanObject {
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    v___x_4136_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1;
    v___x_4137_ = lean_unsigned_to_nat(12);
    v___x_4138_ = lean_unsigned_to_nat(116);
    v___x_4139_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0;
    v___x_4140_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4141_ = l_mkPanicMessageWithDecl(
        v___x_4140_,
        v___x_4139_,
        v___x_4138_,
        v___x_4137_,
        v___x_4136_,
    );
    return v___x_4141_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(
    mut v_k_4142_: *mut LeanObject,
    mut v_decl_4143_: *mut LeanObject,
    mut v_a_4144_: *mut LeanObject,
    mut v_a_4145_: *mut LeanObject,
    mut v_a_4146_: *mut LeanObject,
    mut v_a_4147_: *mut LeanObject,
    mut v_a_4148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v___x_4156_: u8 = 0;
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4165_: u8 = 0;
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4170_: u8 = 0;
    let mut v_reuseFailAlloc_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4150_ = lean_st_ref_take(v_a_4146_);
                v_lctx_4151_ = lean_ctor_get(v___x_4150_, 0);
                v_nextIdx_4152_ = lean_ctor_get(v___x_4150_, 1);
                v_isSharedCheck_4172_ = (!lean_is_exclusive(v___x_4150_)) as u8;
                if v_isSharedCheck_4172_ == 0 {
                    v___x_4154_ = v___x_4150_;
                    v_isShared_4155_ = v_isSharedCheck_4172_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_4152_);
                    lean_inc(v_lctx_4151_);
                    lean_dec(v___x_4150_);
                    v___x_4154_ = lean_box(0);
                    v_isShared_4155_ = v_isSharedCheck_4172_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4156_ = 1;
                lean_inc_ref(v_decl_4143_);
                v___x_4157_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_4156_, v_lctx_4151_, v_decl_4143_);
                if v_isShared_4155_ == 0 {
                    lean_ctor_set(v___x_4154_, 0, v___x_4157_);
                    v___x_4159_ = v___x_4154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4157_);
                    lean_ctor_set(v_reuseFailAlloc_4171_, 1, v_nextIdx_4152_);
                    v___x_4159_ = v_reuseFailAlloc_4171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4160_ = lean_st_ref_set(v_a_4146_, v___x_4159_);
                v___x_4161_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_k_4142_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_,
                    );
                if lean_obj_tag(v___x_4161_) == 0 {
                    v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
                    v_isSharedCheck_4170_ = (!lean_is_exclusive(v___x_4161_)) as u8;
                    if v_isSharedCheck_4170_ == 0 {
                        v___x_4164_ = v___x_4161_;
                        v_isShared_4165_ = v_isSharedCheck_4170_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4162_);
                        lean_dec(v___x_4161_);
                        v___x_4164_ = lean_box(0);
                        v_isShared_4165_ = v_isSharedCheck_4170_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decl_4143_);
                    return v___x_4161_;
                }
            }
            3 => {
                v___x_4166_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4166_, 0, v_decl_4143_);
                lean_ctor_set(v___x_4166_, 1, v_a_4162_);
                if v_isShared_4165_ == 0 {
                    lean_ctor_set(v___x_4164_, 0, v___x_4166_);
                    v___x_4168_ = v___x_4164_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4166_);
                    v___x_4168_ = v_reuseFailAlloc_4169_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(
    mut v_k_4173_: *mut LeanObject,
    mut v_fvarId_4174_: *mut LeanObject,
    mut v_a_4175_: *mut LeanObject,
    mut v_a_4176_: *mut LeanObject,
    mut v_a_4177_: *mut LeanObject,
    mut v_a_4178_: *mut LeanObject,
    mut v_a_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4181_ = lean_st_ref_take(v_a_4175_);
                v_subst_4182_ = lean_ctor_get(v___x_4181_, 0);
                v_jpParamMask_4183_ = lean_ctor_get(v___x_4181_, 1);
                v_isSharedCheck_4194_ = (!lean_is_exclusive(v___x_4181_)) as u8;
                if v_isSharedCheck_4194_ == 0 {
                    v___x_4185_ = v___x_4181_;
                    v_isShared_4186_ = v_isSharedCheck_4194_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_jpParamMask_4183_);
                    lean_inc(v_subst_4182_);
                    lean_dec(v___x_4181_);
                    v___x_4185_ = lean_box(0);
                    v_isShared_4186_ = v_isSharedCheck_4194_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4187_ = lean_box(0);
                v___x_4188_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_4182_, v_fvarId_4174_, v___x_4187_);
                if v_isShared_4186_ == 0 {
                    lean_ctor_set(v___x_4185_, 0, v___x_4188_);
                    v___x_4190_ = v___x_4185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4188_);
                    lean_ctor_set(v_reuseFailAlloc_4193_, 1, v_jpParamMask_4183_);
                    v___x_4190_ = v_reuseFailAlloc_4193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4191_ = lean_st_ref_set(v_a_4175_, v___x_4190_);
                v___x_4192_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_k_4173_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_,
                    );
                return v___x_4192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(
    mut v_decl_4196_: *mut LeanObject,
    mut v_k_4197_: *mut LeanObject,
    mut v_name_4198_: *mut LeanObject,
    mut v_numParams_4199_: *mut LeanObject,
    mut v_args_4200_: *mut LeanObject,
    mut v_a_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
    mut v_a_4205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: u8 = 0;
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4245_: u8 = 0;
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_reuseFailAlloc_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut v_a_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4262_: u8 = 0;
    let mut v_a_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v_isSharedCheck_4271_: u8 = 0;
    let mut v_unused_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4207_ = lean_ctor_get(v_decl_4196_, 0);
                v_binderName_4208_ = lean_ctor_get(v_decl_4196_, 1);
                v_type_4209_ = lean_ctor_get(v_decl_4196_, 2);
                v_isSharedCheck_4271_ = (!lean_is_exclusive(v_decl_4196_)) as u8;
                if v_isSharedCheck_4271_ == 0 {
                    v_unused_4272_ = lean_ctor_get(v_decl_4196_, 3);
                    lean_dec(v_unused_4272_);
                    v___x_4211_ = v_decl_4196_;
                    v_isShared_4212_ = v_isSharedCheck_4271_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_type_4209_);
                    lean_inc(v_binderName_4208_);
                    lean_inc(v_fvarId_4207_);
                    lean_dec(v_decl_4196_);
                    v___x_4211_ = lean_box(0);
                    v_isShared_4212_ = v_isSharedCheck_4271_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4213_ = l_Lean_Compiler_LCNF_toImpureType(v_type_4209_, v_a_4204_, v_a_4205_);
                if lean_obj_tag(v___x_4213_) == 0 {
                    v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
                    lean_inc(v_a_4214_);
                    lean_dec_ref_known(v___x_4213_, 1);
                    v___x_4215_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_4199_);
                    v___x_4216_ =
                        l_Array_extract___redArg(v_args_4200_, v___x_4215_, v_numParams_4199_);
                    v___x_4217_ = 1;
                    v___x_4218_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0;
                    lean_inc(v_binderName_4208_);
                    v___x_4219_ = l_Lean_Name_str___override(v_binderName_4208_, v___x_4218_);
                    v___x_4220_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
                    v___x_4221_ = lean_alloc_ctor(9, 2, (0) as u32);
                    lean_ctor_set(v___x_4221_, 0, v_name_4198_);
                    lean_ctor_set(v___x_4221_, 1, v___x_4216_);
                    v___x_4222_ = l_Lean_Compiler_LCNF_mkLetDecl(
                        v___x_4217_,
                        v___x_4219_,
                        v___x_4220_,
                        v___x_4221_,
                        v_a_4202_,
                        v_a_4203_,
                        v_a_4204_,
                        v_a_4205_,
                    );
                    if lean_obj_tag(v___x_4222_) == 0 {
                        v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
                        lean_inc(v_a_4223_);
                        lean_dec_ref_known(v___x_4222_, 1);
                        v_fvarId_4224_ = lean_ctor_get(v_a_4223_, 0);
                        v___x_4225_ = lean_st_ref_take(v_a_4203_);
                        v_lctx_4226_ = lean_ctor_get(v___x_4225_, 0);
                        v_nextIdx_4227_ = lean_ctor_get(v___x_4225_, 1);
                        v_isSharedCheck_4254_ = (!lean_is_exclusive(v___x_4225_)) as u8;
                        if v_isSharedCheck_4254_ == 0 {
                            v___x_4229_ = v___x_4225_;
                            v_isShared_4230_ = v_isSharedCheck_4254_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_nextIdx_4227_);
                            lean_inc(v_lctx_4226_);
                            lean_dec(v___x_4225_);
                            v___x_4229_ = lean_box(0);
                            v_isShared_4230_ = v_isSharedCheck_4254_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4214_);
                        lean_del_object(v___x_4211_);
                        lean_dec(v_binderName_4208_);
                        lean_dec(v_fvarId_4207_);
                        lean_dec(v_numParams_4199_);
                        lean_dec_ref(v_k_4197_);
                        v_a_4255_ = lean_ctor_get(v___x_4222_, 0);
                        v_isSharedCheck_4262_ = (!lean_is_exclusive(v___x_4222_)) as u8;
                        if v_isSharedCheck_4262_ == 0 {
                            v___x_4257_ = v___x_4222_;
                            v_isShared_4258_ = v_isSharedCheck_4262_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4255_);
                            lean_dec(v___x_4222_);
                            v___x_4257_ = lean_box(0);
                            v_isShared_4258_ = v_isSharedCheck_4262_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4211_);
                    lean_dec(v_binderName_4208_);
                    lean_dec(v_fvarId_4207_);
                    lean_dec(v_numParams_4199_);
                    lean_dec(v_name_4198_);
                    lean_dec_ref(v_k_4197_);
                    v_a_4263_ = lean_ctor_get(v___x_4213_, 0);
                    v_isSharedCheck_4270_ = (!lean_is_exclusive(v___x_4213_)) as u8;
                    if v_isSharedCheck_4270_ == 0 {
                        v___x_4265_ = v___x_4213_;
                        v_isShared_4266_ = v_isSharedCheck_4270_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4263_);
                        lean_dec(v___x_4213_);
                        v___x_4265_ = lean_box(0);
                        v_isShared_4266_ = v_isSharedCheck_4270_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4231_ = lean_array_get_size(v_args_4200_);
                v___x_4232_ =
                    l_Array_extract___redArg(v_args_4200_, v_numParams_4199_, v___x_4231_);
                lean_inc(v_fvarId_4224_);
                v___x_4233_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4233_, 0, v_fvarId_4224_);
                lean_ctor_set(v___x_4233_, 1, v___x_4232_);
                v___x_4234_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_4214_);
                lean_dec(v_a_4214_);
                if v_isShared_4212_ == 0 {
                    lean_ctor_set(v___x_4211_, 3, v___x_4233_);
                    lean_ctor_set(v___x_4211_, 2, v___x_4234_);
                    v___x_4236_ = v___x_4211_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_fvarId_4207_);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_binderName_4208_);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 2, v___x_4234_);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 3, v___x_4233_);
                    v___x_4236_ = v_reuseFailAlloc_4253_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_4236_);
                v___x_4237_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_4217_, v_lctx_4226_, v___x_4236_);
                if v_isShared_4230_ == 0 {
                    lean_ctor_set(v___x_4229_, 0, v___x_4237_);
                    v___x_4239_ = v___x_4229_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4237_);
                    lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_nextIdx_4227_);
                    v___x_4239_ = v_reuseFailAlloc_4252_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4240_ = lean_st_ref_set(v_a_4203_, v___x_4239_);
                v___x_4241_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_k_4197_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                    );
                if lean_obj_tag(v___x_4241_) == 0 {
                    v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
                    v_isSharedCheck_4251_ = (!lean_is_exclusive(v___x_4241_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4244_ = v___x_4241_;
                        v_isShared_4245_ = v_isSharedCheck_4251_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4242_);
                        lean_dec(v___x_4241_);
                        v___x_4244_ = lean_box(0);
                        v_isShared_4245_ = v_isSharedCheck_4251_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4236_);
                    lean_dec(v_a_4223_);
                    return v___x_4241_;
                }
            }
            5 => {
                v___x_4246_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4246_, 0, v___x_4236_);
                lean_ctor_set(v___x_4246_, 1, v_a_4242_);
                v___x_4247_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4247_, 0, v_a_4223_);
                lean_ctor_set(v___x_4247_, 1, v___x_4246_);
                if v_isShared_4245_ == 0 {
                    lean_ctor_set(v___x_4244_, 0, v___x_4247_);
                    v___x_4249_ = v___x_4244_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
                    v___x_4249_ = v_reuseFailAlloc_4250_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4249_;
            }
            7 => {
                if v_isShared_4258_ == 0 {
                    v___x_4260_ = v___x_4257_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
                    v___x_4260_ = v_reuseFailAlloc_4261_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4260_;
            }
            9 => {
                if v_isShared_4266_ == 0 {
                    v___x_4268_ = v___x_4265_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
                    v___x_4268_ = v_reuseFailAlloc_4269_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(
    mut v_decl_4273_: *mut LeanObject,
    mut v_k_4274_: *mut LeanObject,
    mut v_name_4275_: *mut LeanObject,
    mut v_args_4276_: *mut LeanObject,
    mut v_a_4277_: *mut LeanObject,
    mut v_a_4278_: *mut LeanObject,
    mut v_a_4279_: *mut LeanObject,
    mut v_a_4280_: *mut LeanObject,
    mut v_a_4281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4299_: u8 = 0;
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut v_isSharedCheck_4304_: u8 = 0;
    let mut v_unused_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4283_ = lean_ctor_get(v_decl_4273_, 0);
                v_binderName_4284_ = lean_ctor_get(v_decl_4273_, 1);
                v_type_4285_ = lean_ctor_get(v_decl_4273_, 2);
                v_isSharedCheck_4304_ = (!lean_is_exclusive(v_decl_4273_)) as u8;
                if v_isSharedCheck_4304_ == 0 {
                    v_unused_4305_ = lean_ctor_get(v_decl_4273_, 3);
                    lean_dec(v_unused_4305_);
                    v___x_4287_ = v_decl_4273_;
                    v_isShared_4288_ = v_isSharedCheck_4304_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_type_4285_);
                    lean_inc(v_binderName_4284_);
                    lean_inc(v_fvarId_4283_);
                    lean_dec(v_decl_4273_);
                    v___x_4287_ = lean_box(0);
                    v_isShared_4288_ = v_isSharedCheck_4304_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4289_ = l_Lean_Compiler_LCNF_toImpureType(v_type_4285_, v_a_4280_, v_a_4281_);
                if lean_obj_tag(v___x_4289_) == 0 {
                    v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
                    lean_inc(v_a_4290_);
                    lean_dec_ref_known(v___x_4289_, 1);
                    v___x_4291_ = lean_alloc_ctor(9, 2, (0) as u32);
                    lean_ctor_set(v___x_4291_, 0, v_name_4275_);
                    lean_ctor_set(v___x_4291_, 1, v_args_4276_);
                    if v_isShared_4288_ == 0 {
                        lean_ctor_set(v___x_4287_, 3, v___x_4291_);
                        lean_ctor_set(v___x_4287_, 2, v_a_4290_);
                        v___x_4293_ = v___x_4287_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_fvarId_4283_);
                        lean_ctor_set(v_reuseFailAlloc_4295_, 1, v_binderName_4284_);
                        lean_ctor_set(v_reuseFailAlloc_4295_, 2, v_a_4290_);
                        lean_ctor_set(v_reuseFailAlloc_4295_, 3, v___x_4291_);
                        v___x_4293_ = v_reuseFailAlloc_4295_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4287_);
                    lean_dec(v_binderName_4284_);
                    lean_dec(v_fvarId_4283_);
                    lean_dec_ref(v_args_4276_);
                    lean_dec(v_name_4275_);
                    lean_dec_ref(v_k_4274_);
                    v_a_4296_ = lean_ctor_get(v___x_4289_, 0);
                    v_isSharedCheck_4303_ = (!lean_is_exclusive(v___x_4289_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v___x_4298_ = v___x_4289_;
                        v_isShared_4299_ = v_isSharedCheck_4303_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4296_);
                        lean_dec(v___x_4289_);
                        v___x_4298_ = lean_box(0);
                        v_isShared_4299_ = v_isSharedCheck_4303_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4294_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_4274_, v___x_4293_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
                return v___x_4294_;
            }
            3 => {
                if v_isShared_4299_ == 0 {
                    v___x_4301_ = v___x_4298_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
                    v___x_4301_ = v_reuseFailAlloc_4302_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(
    mut v_decl_4306_: *mut LeanObject,
    mut v_k_4307_: *mut LeanObject,
    mut v_name_4308_: *mut LeanObject,
    mut v_args_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4320_: u8 = 0;
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4327_: u8 = 0;
    let mut v_unused_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_4316_ = lean_ctor_get(v_decl_4306_, 0);
                v_binderName_4317_ = lean_ctor_get(v_decl_4306_, 1);
                v_isSharedCheck_4327_ = (!lean_is_exclusive(v_decl_4306_)) as u8;
                if v_isSharedCheck_4327_ == 0 {
                    v_unused_4328_ = lean_ctor_get(v_decl_4306_, 3);
                    lean_dec(v_unused_4328_);
                    v_unused_4329_ = lean_ctor_get(v_decl_4306_, 2);
                    lean_dec(v_unused_4329_);
                    v___x_4319_ = v_decl_4306_;
                    v_isShared_4320_ = v_isSharedCheck_4327_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_binderName_4317_);
                    lean_inc(v_fvarId_4316_);
                    lean_dec(v_decl_4306_);
                    v___x_4319_ = lean_box(0);
                    v_isShared_4320_ = v_isSharedCheck_4327_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4321_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
                v___x_4322_ = lean_alloc_ctor(10, 2, (0) as u32);
                lean_ctor_set(v___x_4322_, 0, v_name_4308_);
                lean_ctor_set(v___x_4322_, 1, v_args_4309_);
                if v_isShared_4320_ == 0 {
                    lean_ctor_set(v___x_4319_, 3, v___x_4322_);
                    lean_ctor_set(v___x_4319_, 2, v___x_4321_);
                    v___x_4324_ = v___x_4319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_fvarId_4316_);
                    lean_ctor_set(v_reuseFailAlloc_4326_, 1, v_binderName_4317_);
                    lean_ctor_set(v_reuseFailAlloc_4326_, 2, v___x_4321_);
                    lean_ctor_set(v_reuseFailAlloc_4326_, 3, v___x_4322_);
                    v___x_4324_ = v_reuseFailAlloc_4326_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4325_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_4307_, v___x_4324_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
                return v___x_4325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(
    mut v_decl_4330_: *mut LeanObject,
    mut v_k_4331_: *mut LeanObject,
    mut v_name_4332_: *mut LeanObject,
    mut v_numParams_4333_: *mut LeanObject,
    mut v_args_4334_: *mut LeanObject,
    mut v_a_4335_: *mut LeanObject,
    mut v_a_4336_: *mut LeanObject,
    mut v_a_4337_: *mut LeanObject,
    mut v_a_4338_: *mut LeanObject,
    mut v_a_4339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numArgs_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: u8 = 0;
    v_numArgs_4341_ = lean_array_get_size(v_args_4334_);
    v___x_4342_ = lean_nat_dec_lt(v_numArgs_4341_, v_numParams_4333_);
    if v___x_4342_ == 0 {
        let mut v___x_4343_: u8 = 0;
        v___x_4343_ = lean_nat_dec_eq(v_numArgs_4341_, v_numParams_4333_);
        if v___x_4343_ == 0 {
            let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
            v___x_4344_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_4330_, v_k_4331_, v_name_4332_, v_numParams_4333_, v_args_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
            lean_dec_ref(v_args_4334_);
            return v___x_4344_;
        } else {
            let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_numParams_4333_);
            v___x_4345_ =
                l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(
                    v_decl_4330_,
                    v_k_4331_,
                    v_name_4332_,
                    v_args_4334_,
                    v_a_4335_,
                    v_a_4336_,
                    v_a_4337_,
                    v_a_4338_,
                    v_a_4339_,
                );
            return v___x_4345_;
        }
    } else {
        let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_numParams_4333_);
        v___x_4346_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(
            v_decl_4330_,
            v_k_4331_,
            v_name_4332_,
            v_args_4334_,
            v_a_4335_,
            v_a_4336_,
            v_a_4337_,
            v_a_4338_,
            v_a_4339_,
        );
        return v___x_4346_;
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4()
-> *mut LeanObject {
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    v___x_4348_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3;
    v___x_4349_ = lean_unsigned_to_nat(14);
    v___x_4350_ = lean_unsigned_to_nat(185);
    v___x_4351_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0;
    v___x_4352_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4353_ = l_mkPanicMessageWithDecl(
        v___x_4352_,
        v___x_4351_,
        v___x_4350_,
        v___x_4349_,
        v___x_4348_,
    );
    return v___x_4353_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9()
-> *mut LeanObject {
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    v___x_4360_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
    v___x_4361_ = lean_alloc_ctor(6, 1, (0) as u32);
    lean_ctor_set(v___x_4361_, 0, v___x_4360_);
    return v___x_4361_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(
    mut v_decl_4370_: *mut LeanObject,
    mut v_k_4371_: *mut LeanObject,
    mut v_a_4372_: *mut LeanObject,
    mut v_a_4373_: *mut LeanObject,
    mut v_a_4374_: *mut LeanObject,
    mut v_a_4375_: *mut LeanObject,
    mut v_a_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4394_: u8 = 0;
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4396_: u8 = 0;
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v_value_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_unused_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v_typeName_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v_fieldIdx_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4447_: u8 = 0;
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4463_: u8 = 0;
    let mut v_isSharedCheck_4464_: u8 = 0;
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorInfo_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInfo_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4499_: u8 = 0;
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_a_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4521_: u8 = 0;
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_unused_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4529_: usize = 0;
    let mut v___x_4530_: usize = 0;
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: u8 = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v_unused_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut v_unused_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4589_: u8 = 0;
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_unused_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4619_: u8 = 0;
    let mut v_unused_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v_induct_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldIdx_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4648_: u8 = 0;
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: u8 = 0;
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorInfo_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInfo_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: u8 = 0;
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut v_reuseFailAlloc_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4705_: u8 = 0;
    let mut v_a_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4713_: u8 = 0;
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut v_isSharedCheck_4715_: u8 = 0;
    let mut v_a_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4723_: u8 = 0;
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4726_: u8 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4735_: u8 = 0;
    let mut v_unused_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4743_: u8 = 0;
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4747_: u8 = 0;
    let mut v_a_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4755_: u8 = 0;
    let mut v_isSharedCheck_4756_: u8 = 0;
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v_unused_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4778_: u8 = 0;
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4782_: u8 = 0;
    let mut v_a_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4786_: u8 = 0;
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4790_: u8 = 0;
    let mut v_a_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4794_: u8 = 0;
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4798_: u8 = 0;
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v_fvarId_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4806_: u8 = 0;
    let mut v_sz_4807_: usize = 0;
    let mut v___x_4808_: usize = 0;
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4824_: u8 = 0;
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4828_: u8 = 0;
    let mut v_a_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut v_isSharedCheck_4837_: u8 = 0;
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_unused_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4843_: u8 = 0;
    let mut v_unused_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4386_ = lean_st_ref_get(v_a_4372_);
                v_fvarId_4387_ = lean_ctor_get(v_decl_4370_, 0);
                v_binderName_4388_ = lean_ctor_get(v_decl_4370_, 1);
                v_type_4389_ = lean_ctor_get(v_decl_4370_, 2);
                v_value_4390_ = lean_ctor_get(v_decl_4370_, 3);
                v_subst_4391_ = lean_ctor_get(v___x_4386_, 0);
                v_isSharedCheck_4843_ = (!lean_is_exclusive(v___x_4386_)) as u8;
                if v_isSharedCheck_4843_ == 0 {
                    v_unused_4844_ = lean_ctor_get(v___x_4386_, 1);
                    lean_dec(v_unused_4844_);
                    v___x_4393_ = v___x_4386_;
                    v_isShared_4394_ = v_isSharedCheck_4843_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_subst_4391_);
                    lean_dec(v___x_4386_);
                    v___x_4393_ = lean_box(0);
                    v_isShared_4394_ = v_isSharedCheck_4843_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4384_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
                v___x_4385_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_4384_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
                return v___x_4385_;
            }
            2 => {
                v___x_4395_ = 0;
                v___x_4396_ = 1;
                lean_inc(v_value_4390_);
                v___x_4397_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
                        v___x_4395_,
                        v_subst_4391_,
                        v_value_4390_,
                        v___x_4396_,
                    );
                lean_dec_ref(v_subst_4391_);
                match lean_obj_tag(v___x_4397_) {
                    0 => {
                        lean_inc(v_binderName_4388_);
                        lean_inc(v_fvarId_4387_);
                        lean_del_object(v___x_4393_);
                        v_isSharedCheck_4414_ = (!lean_is_exclusive(v_decl_4370_)) as u8;
                        if v_isSharedCheck_4414_ == 0 {
                            v_unused_4415_ = lean_ctor_get(v_decl_4370_, 3);
                            lean_dec(v_unused_4415_);
                            v_unused_4416_ = lean_ctor_get(v_decl_4370_, 2);
                            lean_dec(v_unused_4416_);
                            v_unused_4417_ = lean_ctor_get(v_decl_4370_, 1);
                            lean_dec(v_unused_4417_);
                            v_unused_4418_ = lean_ctor_get(v_decl_4370_, 0);
                            lean_dec(v_unused_4418_);
                            v___x_4399_ = v_decl_4370_;
                            v_isShared_4400_ = v_isSharedCheck_4414_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_decl_4370_);
                            v___x_4399_ = lean_box(0);
                            v_isShared_4400_ = v_isSharedCheck_4414_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        lean_inc(v_fvarId_4387_);
                        lean_del_object(v___x_4393_);
                        lean_dec_ref(v_decl_4370_);
                        v___x_4419_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_4371_, v_fvarId_4387_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                        return v___x_4419_;
                    }
                    2 => {
                        lean_inc(v_binderName_4388_);
                        lean_inc(v_fvarId_4387_);
                        lean_del_object(v___x_4393_);
                        v_isSharedCheck_4522_ = (!lean_is_exclusive(v_decl_4370_)) as u8;
                        if v_isSharedCheck_4522_ == 0 {
                            v_unused_4523_ = lean_ctor_get(v_decl_4370_, 3);
                            lean_dec(v_unused_4523_);
                            v_unused_4524_ = lean_ctor_get(v_decl_4370_, 2);
                            lean_dec(v_unused_4524_);
                            v_unused_4525_ = lean_ctor_get(v_decl_4370_, 1);
                            lean_dec(v_unused_4525_);
                            v_unused_4526_ = lean_ctor_get(v_decl_4370_, 0);
                            lean_dec(v_unused_4526_);
                            v___x_4421_ = v_decl_4370_;
                            v_isShared_4422_ = v_isSharedCheck_4522_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v_decl_4370_);
                            v___x_4421_ = lean_box(0);
                            v_isShared_4422_ = v_isSharedCheck_4522_;
                            state = 7;
                            continue;
                        }
                    }
                    3 => {
                        v_declName_4527_ = lean_ctor_get(v___x_4397_, 0);
                        lean_inc(v_declName_4527_);
                        v_args_4528_ = lean_ctor_get(v___x_4397_, 2);
                        lean_inc_ref_n(v_args_4528_, 2);
                        lean_dec_ref_known(v___x_4397_, 3);
                        v_sz_4529_ = lean_array_size(v_args_4528_);
                        v___x_4530_ = 0usize;
                        v___x_4531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_4529_, v___x_4530_, v_args_4528_, v_a_4372_);
                        if lean_obj_tag(v___x_4531_) == 0 {
                            v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
                            lean_inc(v_a_4532_);
                            lean_dec_ref_known(v___x_4531_, 1);
                            lean_inc(v_declName_4527_);
                            v___x_4533_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(
                                v_declName_4527_,
                                v_a_4376_,
                            );
                            if lean_obj_tag(v___x_4533_) == 0 {
                                v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
                                lean_inc(v_a_4534_);
                                lean_dec_ref_known(v___x_4533_, 1);
                                if lean_obj_tag(v_a_4534_) == 1 {
                                    lean_dec_ref(v_args_4528_);
                                    lean_del_object(v___x_4393_);
                                    v_val_4535_ = lean_ctor_get(v_a_4534_, 0);
                                    lean_inc(v_val_4535_);
                                    lean_dec_ref_known(v_a_4534_, 1);
                                    v_params_4536_ = lean_ctor_get(v_val_4535_, 3);
                                    lean_inc_ref(v_params_4536_);
                                    lean_dec(v_val_4535_);
                                    v___x_4537_ = lean_array_get_size(v_params_4536_);
                                    lean_dec_ref(v_params_4536_);
                                    v___x_4538_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_4370_, v_k_4371_, v_declName_4527_, v___x_4537_, v_a_4532_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                                    return v___x_4538_;
                                } else {
                                    lean_dec(v_a_4534_);
                                    lean_inc(v_declName_4527_);
                                    v___x_4539_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(
                                        v_declName_4527_,
                                        v_a_4376_,
                                    );
                                    if lean_obj_tag(v___x_4539_) == 0 {
                                        v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
                                        lean_inc(v_a_4540_);
                                        lean_dec_ref_known(v___x_4539_, 1);
                                        if lean_obj_tag(v_a_4540_) == 1 {
                                            lean_dec_ref(v_args_4528_);
                                            lean_del_object(v___x_4393_);
                                            v_val_4541_ = lean_ctor_get(v_a_4540_, 0);
                                            lean_inc(v_val_4541_);
                                            lean_dec_ref_known(v_a_4540_, 1);
                                            v_toSignature_4542_ = lean_ctor_get(v_val_4541_, 0);
                                            lean_inc_ref(v_toSignature_4542_);
                                            lean_dec(v_val_4541_);
                                            v_params_4543_ = lean_ctor_get(v_toSignature_4542_, 3);
                                            lean_inc_ref(v_params_4543_);
                                            lean_dec_ref(v_toSignature_4542_);
                                            v___x_4544_ = lean_array_get_size(v_params_4543_);
                                            lean_dec_ref(v_params_4543_);
                                            v___x_4545_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_4370_, v_k_4371_, v_declName_4527_, v___x_4544_, v_a_4532_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                                            return v___x_4545_;
                                        } else {
                                            lean_dec(v_a_4540_);
                                            v___x_4546_ = lean_st_ref_get(v_a_4376_);
                                            v_env_4547_ = lean_ctor_get(v___x_4546_, 0);
                                            lean_inc_ref(v_env_4547_);
                                            lean_dec(v___x_4546_);
                                            v___x_4548_ = 0;
                                            lean_inc(v_declName_4527_);
                                            v___x_4549_ = l_Lean_Environment_find_x3f(
                                                v_env_4547_,
                                                v_declName_4527_,
                                                v___x_4548_,
                                            );
                                            if lean_obj_tag(v___x_4549_) == 0 {
                                                lean_dec(v_a_4532_);
                                                lean_dec_ref(v_args_4528_);
                                                lean_dec(v_declName_4527_);
                                                lean_del_object(v___x_4393_);
                                                lean_dec_ref(v_k_4371_);
                                                lean_dec_ref(v_decl_4370_);
                                                v___x_4550_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
                                                v___x_4551_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_4550_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                                                return v___x_4551_;
                                            } else {
                                                v_val_4552_ = lean_ctor_get(v___x_4549_, 0);
                                                lean_inc(v_val_4552_);
                                                lean_dec_ref_known(v___x_4549_, 1);
                                                match lean_obj_tag(v_val_4552_) {
                                                    0 => {
                                                        lean_dec(v_a_4532_);
                                                        lean_dec_ref(v_args_4528_);
                                                        lean_dec_ref(v_k_4371_);
                                                        lean_dec_ref(v_decl_4370_);
                                                        v_isSharedCheck_4568_ =
                                                            (!lean_is_exclusive(v_val_4552_)) as u8;
                                                        if v_isSharedCheck_4568_ == 0 {
                                                            v_unused_4569_ =
                                                                lean_ctor_get(v_val_4552_, 0);
                                                            lean_dec(v_unused_4569_);
                                                            v___x_4554_ = v_val_4552_;
                                                            v_isShared_4555_ =
                                                                v_isSharedCheck_4568_;
                                                            state = 21;
                                                            continue;
                                                        } else {
                                                            lean_dec(v_val_4552_);
                                                            v___x_4554_ = lean_box(0);
                                                            v_isShared_4555_ =
                                                                v_isSharedCheck_4568_;
                                                            state = 21;
                                                            continue;
                                                        }
                                                    }
                                                    2 => {
                                                        lean_dec(v_a_4532_);
                                                        lean_dec_ref(v_args_4528_);
                                                        lean_dec_ref(v_k_4371_);
                                                        lean_dec_ref(v_decl_4370_);
                                                        v_isSharedCheck_4585_ =
                                                            (!lean_is_exclusive(v_val_4552_)) as u8;
                                                        if v_isSharedCheck_4585_ == 0 {
                                                            v_unused_4586_ =
                                                                lean_ctor_get(v_val_4552_, 0);
                                                            lean_dec(v_unused_4586_);
                                                            v___x_4571_ = v_val_4552_;
                                                            v_isShared_4572_ =
                                                                v_isSharedCheck_4585_;
                                                            state = 24;
                                                            continue;
                                                        } else {
                                                            lean_dec(v_val_4552_);
                                                            v___x_4571_ = lean_box(0);
                                                            v_isShared_4572_ =
                                                                v_isSharedCheck_4585_;
                                                            state = 24;
                                                            continue;
                                                        }
                                                    }
                                                    4 => {
                                                        lean_dec(v_a_4532_);
                                                        lean_dec_ref(v_args_4528_);
                                                        lean_dec_ref(v_k_4371_);
                                                        lean_dec_ref(v_decl_4370_);
                                                        v_isSharedCheck_4602_ =
                                                            (!lean_is_exclusive(v_val_4552_)) as u8;
                                                        if v_isSharedCheck_4602_ == 0 {
                                                            v_unused_4603_ =
                                                                lean_ctor_get(v_val_4552_, 0);
                                                            lean_dec(v_unused_4603_);
                                                            v___x_4588_ = v_val_4552_;
                                                            v_isShared_4589_ =
                                                                v_isSharedCheck_4602_;
                                                            state = 27;
                                                            continue;
                                                        } else {
                                                            lean_dec(v_val_4552_);
                                                            v___x_4588_ = lean_box(0);
                                                            v_isShared_4589_ =
                                                                v_isSharedCheck_4602_;
                                                            state = 27;
                                                            continue;
                                                        }
                                                    }
                                                    5 => {
                                                        lean_dec(v_a_4532_);
                                                        lean_dec_ref(v_args_4528_);
                                                        lean_dec_ref(v_k_4371_);
                                                        lean_dec_ref(v_decl_4370_);
                                                        v_isSharedCheck_4619_ =
                                                            (!lean_is_exclusive(v_val_4552_)) as u8;
                                                        if v_isSharedCheck_4619_ == 0 {
                                                            v_unused_4620_ =
                                                                lean_ctor_get(v_val_4552_, 0);
                                                            lean_dec(v_unused_4620_);
                                                            v___x_4605_ = v_val_4552_;
                                                            v_isShared_4606_ =
                                                                v_isSharedCheck_4619_;
                                                            state = 30;
                                                            continue;
                                                        } else {
                                                            lean_dec(v_val_4552_);
                                                            v___x_4605_ = lean_box(0);
                                                            v_isShared_4606_ =
                                                                v_isSharedCheck_4619_;
                                                            state = 30;
                                                            continue;
                                                        }
                                                    }
                                                    6 => {
                                                        v_val_4621_ = lean_ctor_get(v_val_4552_, 0);
                                                        v_isSharedCheck_4756_ =
                                                            (!lean_is_exclusive(v_val_4552_)) as u8;
                                                        if v_isSharedCheck_4756_ == 0 {
                                                            v___x_4623_ = v_val_4552_;
                                                            v_isShared_4624_ =
                                                                v_isSharedCheck_4756_;
                                                            state = 33;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_val_4621_);
                                                            lean_dec(v_val_4552_);
                                                            v___x_4623_ = lean_box(0);
                                                            v_isShared_4624_ =
                                                                v_isSharedCheck_4756_;
                                                            state = 33;
                                                            continue;
                                                        }
                                                    }
                                                    7 => {
                                                        lean_dec(v_a_4532_);
                                                        lean_dec_ref(v_args_4528_);
                                                        lean_dec_ref(v_k_4371_);
                                                        lean_dec_ref(v_decl_4370_);
                                                        v_isSharedCheck_4772_ =
                                                            (!lean_is_exclusive(v_val_4552_)) as u8;
                                                        if v_isSharedCheck_4772_ == 0 {
                                                            v_unused_4773_ =
                                                                lean_ctor_get(v_val_4552_, 0);
                                                            lean_dec(v_unused_4773_);
                                                            v___x_4758_ = v_val_4552_;
                                                            v_isShared_4759_ =
                                                                v_isSharedCheck_4772_;
                                                            state = 57;
                                                            continue;
                                                        } else {
                                                            lean_dec(v_val_4552_);
                                                            v___x_4758_ = lean_box(0);
                                                            v_isShared_4759_ =
                                                                v_isSharedCheck_4772_;
                                                            state = 57;
                                                            continue;
                                                        }
                                                    }
                                                    _ => {
                                                        lean_dec(v_val_4552_);
                                                        lean_dec_ref(v_args_4528_);
                                                        lean_del_object(v___x_4393_);
                                                        v___x_4774_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_4370_, v_k_4371_, v_declName_4527_, v_a_4532_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                                                        return v___x_4774_;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_4532_);
                                        lean_dec_ref(v_args_4528_);
                                        lean_dec(v_declName_4527_);
                                        lean_del_object(v___x_4393_);
                                        lean_dec_ref(v_k_4371_);
                                        lean_dec_ref(v_decl_4370_);
                                        v_a_4775_ = lean_ctor_get(v___x_4539_, 0);
                                        v_isSharedCheck_4782_ =
                                            (!lean_is_exclusive(v___x_4539_)) as u8;
                                        if v_isSharedCheck_4782_ == 0 {
                                            v___x_4777_ = v___x_4539_;
                                            v_isShared_4778_ = v_isSharedCheck_4782_;
                                            state = 60;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4775_);
                                            lean_dec(v___x_4539_);
                                            v___x_4777_ = lean_box(0);
                                            v_isShared_4778_ = v_isSharedCheck_4782_;
                                            state = 60;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_a_4532_);
                                lean_dec_ref(v_args_4528_);
                                lean_dec(v_declName_4527_);
                                lean_del_object(v___x_4393_);
                                lean_dec_ref(v_k_4371_);
                                lean_dec_ref(v_decl_4370_);
                                v_a_4783_ = lean_ctor_get(v___x_4533_, 0);
                                v_isSharedCheck_4790_ = (!lean_is_exclusive(v___x_4533_)) as u8;
                                if v_isSharedCheck_4790_ == 0 {
                                    v___x_4785_ = v___x_4533_;
                                    v_isShared_4786_ = v_isSharedCheck_4790_;
                                    state = 62;
                                    continue;
                                } else {
                                    lean_inc(v_a_4783_);
                                    lean_dec(v___x_4533_);
                                    v___x_4785_ = lean_box(0);
                                    v_isShared_4786_ = v_isSharedCheck_4790_;
                                    state = 62;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_args_4528_);
                            lean_dec(v_declName_4527_);
                            lean_del_object(v___x_4393_);
                            lean_dec_ref(v_k_4371_);
                            lean_dec_ref(v_decl_4370_);
                            v_a_4791_ = lean_ctor_get(v___x_4531_, 0);
                            v_isSharedCheck_4798_ = (!lean_is_exclusive(v___x_4531_)) as u8;
                            if v_isSharedCheck_4798_ == 0 {
                                v___x_4793_ = v___x_4531_;
                                v_isShared_4794_ = v_isSharedCheck_4798_;
                                state = 64;
                                continue;
                            } else {
                                lean_inc(v_a_4791_);
                                lean_dec(v___x_4531_);
                                v___x_4793_ = lean_box(0);
                                v_isShared_4794_ = v_isSharedCheck_4798_;
                                state = 64;
                                continue;
                            }
                        }
                    }
                    _ => {
                        lean_inc_ref(v_type_4389_);
                        lean_inc(v_binderName_4388_);
                        lean_inc(v_fvarId_4387_);
                        lean_del_object(v___x_4393_);
                        v_isSharedCheck_4838_ = (!lean_is_exclusive(v_decl_4370_)) as u8;
                        if v_isSharedCheck_4838_ == 0 {
                            v_unused_4839_ = lean_ctor_get(v_decl_4370_, 3);
                            lean_dec(v_unused_4839_);
                            v_unused_4840_ = lean_ctor_get(v_decl_4370_, 2);
                            lean_dec(v_unused_4840_);
                            v_unused_4841_ = lean_ctor_get(v_decl_4370_, 1);
                            lean_dec(v_unused_4841_);
                            v_unused_4842_ = lean_ctor_get(v_decl_4370_, 0);
                            lean_dec(v_unused_4842_);
                            v___x_4800_ = v_decl_4370_;
                            v_isShared_4801_ = v_isSharedCheck_4838_;
                            state = 66;
                            continue;
                        } else {
                            lean_dec(v_decl_4370_);
                            v___x_4800_ = lean_box(0);
                            v_isShared_4801_ = v_isSharedCheck_4838_;
                            state = 66;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_value_4401_ = lean_ctor_get(v___x_4397_, 0);
                v_isSharedCheck_4413_ = (!lean_is_exclusive(v___x_4397_)) as u8;
                if v_isSharedCheck_4413_ == 0 {
                    v___x_4403_ = v___x_4397_;
                    v_isShared_4404_ = v_isSharedCheck_4413_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_value_4401_);
                    lean_dec(v___x_4397_);
                    v___x_4403_ = lean_box(0);
                    v_isShared_4404_ = v_isSharedCheck_4413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4405_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_4401_);
                if v_isShared_4404_ == 0 {
                    v___x_4407_ = v___x_4403_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_value_4401_);
                    v___x_4407_ = v_reuseFailAlloc_4412_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4400_ == 0 {
                    lean_ctor_set(v___x_4399_, 3, v___x_4407_);
                    lean_ctor_set(v___x_4399_, 2, v___x_4405_);
                    v___x_4409_ = v___x_4399_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_fvarId_4387_);
                    lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_binderName_4388_);
                    lean_ctor_set(v_reuseFailAlloc_4411_, 2, v___x_4405_);
                    lean_ctor_set(v_reuseFailAlloc_4411_, 3, v___x_4407_);
                    v___x_4409_ = v_reuseFailAlloc_4411_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4410_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_4371_, v___x_4409_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4410_;
            }
            7 => {
                v_typeName_4423_ = lean_ctor_get(v___x_4397_, 0);
                lean_inc_n(v_typeName_4423_, 2);
                v_idx_4424_ = lean_ctor_get(v___x_4397_, 1);
                lean_inc(v_idx_4424_);
                v_struct_4425_ = lean_ctor_get(v___x_4397_, 2);
                lean_inc(v_struct_4425_);
                lean_dec_ref_known(v___x_4397_, 3);
                v___x_4426_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(
                    v_typeName_4423_,
                    v_a_4375_,
                    v_a_4376_,
                );
                if lean_obj_tag(v___x_4426_) == 0 {
                    v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
                    lean_inc(v_a_4427_);
                    lean_dec_ref_known(v___x_4426_, 1);
                    if lean_obj_tag(v_a_4427_) == 1 {
                        lean_dec(v_typeName_4423_);
                        lean_del_object(v___x_4421_);
                        lean_dec(v_binderName_4388_);
                        v_val_4428_ = lean_ctor_get(v_a_4427_, 0);
                        v_isSharedCheck_4464_ = (!lean_is_exclusive(v_a_4427_)) as u8;
                        if v_isSharedCheck_4464_ == 0 {
                            v___x_4430_ = v_a_4427_;
                            v_isShared_4431_ = v_isSharedCheck_4464_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_val_4428_);
                            lean_dec(v_a_4427_);
                            v___x_4430_ = lean_box(0);
                            v_isShared_4431_ = v_isSharedCheck_4464_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4427_);
                        v___x_4465_ = lean_st_ref_get(v_a_4372_);
                        v_subst_4466_ = lean_ctor_get(v___x_4465_, 0);
                        lean_inc_ref(v_subst_4466_);
                        lean_dec(v___x_4465_);
                        v___x_4467_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_subst_4466_,
                            v_struct_4425_,
                            v___x_4396_,
                        );
                        lean_dec_ref(v_subst_4466_);
                        if lean_obj_tag(v___x_4467_) == 0 {
                            v_fvarId_4468_ = lean_ctor_get(v___x_4467_, 0);
                            lean_inc(v_fvarId_4468_);
                            lean_dec_ref_known(v___x_4467_, 1);
                            v___x_4469_ = lean_st_ref_get(v_a_4376_);
                            v_env_4470_ = lean_ctor_get(v___x_4469_, 0);
                            lean_inc_ref(v_env_4470_);
                            lean_dec(v___x_4469_);
                            v___x_4471_ = 0;
                            v___x_4472_ = l_Lean_Environment_find_x3f(
                                v_env_4470_,
                                v_typeName_4423_,
                                v___x_4471_,
                            );
                            if lean_obj_tag(v___x_4472_) == 1 {
                                v_val_4473_ = lean_ctor_get(v___x_4472_, 0);
                                lean_inc(v_val_4473_);
                                lean_dec_ref_known(v___x_4472_, 1);
                                if lean_obj_tag(v_val_4473_) == 5 {
                                    v_val_4474_ = lean_ctor_get(v_val_4473_, 0);
                                    lean_inc_ref(v_val_4474_);
                                    lean_dec_ref_known(v_val_4473_, 1);
                                    v_ctors_4475_ = lean_ctor_get(v_val_4474_, 4);
                                    lean_inc(v_ctors_4475_);
                                    lean_dec_ref(v_val_4474_);
                                    if lean_obj_tag(v_ctors_4475_) == 1 {
                                        v_tail_4476_ = lean_ctor_get(v_ctors_4475_, 1);
                                        if lean_obj_tag(v_tail_4476_) == 0 {
                                            v_head_4477_ = lean_ctor_get(v_ctors_4475_, 0);
                                            lean_inc(v_head_4477_);
                                            lean_dec_ref_known(v_ctors_4475_, 2);
                                            v___x_4478_ = l_Lean_Compiler_LCNF_getCtorLayout(
                                                v_head_4477_,
                                                v_a_4375_,
                                                v_a_4376_,
                                            );
                                            if lean_obj_tag(v___x_4478_) == 0 {
                                                v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
                                                lean_inc(v_a_4479_);
                                                lean_dec_ref_known(v___x_4478_, 1);
                                                v_ctorInfo_4480_ = lean_ctor_get(v_a_4479_, 0);
                                                lean_inc_ref(v_ctorInfo_4480_);
                                                v_fieldInfo_4481_ = lean_ctor_get(v_a_4479_, 1);
                                                lean_inc_ref(v_fieldInfo_4481_);
                                                lean_dec(v_a_4479_);
                                                v___x_4482_ = lean_box(0);
                                                v___x_4483_ = lean_array_get(
                                                    v___x_4482_,
                                                    v_fieldInfo_4481_,
                                                    v_idx_4424_,
                                                );
                                                lean_dec(v_idx_4424_);
                                                lean_dec_ref(v_fieldInfo_4481_);
                                                v___x_4484_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_4468_, v_ctorInfo_4480_, v___x_4483_);
                                                lean_dec_ref(v_ctorInfo_4480_);
                                                v_fst_4485_ = lean_ctor_get(v___x_4484_, 0);
                                                lean_inc(v_fst_4485_);
                                                if lean_obj_tag(v_fst_4485_) == 1 {
                                                    lean_dec_ref(v___x_4484_);
                                                    lean_del_object(v___x_4421_);
                                                    lean_dec(v_binderName_4388_);
                                                    v___x_4486_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_4371_, v_fvarId_4387_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                                                    return v___x_4486_;
                                                } else {
                                                    v_snd_4487_ = lean_ctor_get(v___x_4484_, 1);
                                                    lean_inc(v_snd_4487_);
                                                    lean_dec_ref(v___x_4484_);
                                                    if v_isShared_4422_ == 0 {
                                                        lean_ctor_set(v___x_4421_, 3, v_fst_4485_);
                                                        lean_ctor_set(v___x_4421_, 2, v_snd_4487_);
                                                        v___x_4489_ = v___x_4421_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_4491_ =
                                                            lean_alloc_ctor(0, 4, (0) as u32);
                                                        lean_ctor_set(
                                                            v_reuseFailAlloc_4491_,
                                                            0,
                                                            v_fvarId_4387_,
                                                        );
                                                        lean_ctor_set(
                                                            v_reuseFailAlloc_4491_,
                                                            1,
                                                            v_binderName_4388_,
                                                        );
                                                        lean_ctor_set(
                                                            v_reuseFailAlloc_4491_,
                                                            2,
                                                            v_snd_4487_,
                                                        );
                                                        lean_ctor_set(
                                                            v_reuseFailAlloc_4491_,
                                                            3,
                                                            v_fst_4485_,
                                                        );
                                                        v___x_4489_ = v_reuseFailAlloc_4491_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_fvarId_4468_);
                                                lean_dec(v_idx_4424_);
                                                lean_del_object(v___x_4421_);
                                                lean_dec(v_binderName_4388_);
                                                lean_dec(v_fvarId_4387_);
                                                lean_dec_ref(v_k_4371_);
                                                v_a_4492_ = lean_ctor_get(v___x_4478_, 0);
                                                v_isSharedCheck_4499_ =
                                                    (!lean_is_exclusive(v___x_4478_)) as u8;
                                                if v_isSharedCheck_4499_ == 0 {
                                                    v___x_4494_ = v___x_4478_;
                                                    v_isShared_4495_ = v_isSharedCheck_4499_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4492_);
                                                    lean_dec(v___x_4478_);
                                                    v___x_4494_ = lean_box(0);
                                                    v_isShared_4495_ = v_isSharedCheck_4499_;
                                                    state = 15;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref_known(v_ctors_4475_, 2);
                                            lean_dec(v_fvarId_4468_);
                                            lean_dec(v_idx_4424_);
                                            lean_del_object(v___x_4421_);
                                            lean_dec(v_binderName_4388_);
                                            lean_dec(v_fvarId_4387_);
                                            lean_dec_ref(v_k_4371_);
                                            v___y_4379_ = v_a_4372_;
                                            v___y_4380_ = v_a_4373_;
                                            v___y_4381_ = v_a_4374_;
                                            v___y_4382_ = v_a_4375_;
                                            v___y_4383_ = v_a_4376_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_ctors_4475_);
                                        lean_dec(v_fvarId_4468_);
                                        lean_dec(v_idx_4424_);
                                        lean_del_object(v___x_4421_);
                                        lean_dec(v_binderName_4388_);
                                        lean_dec(v_fvarId_4387_);
                                        lean_dec_ref(v_k_4371_);
                                        v___y_4379_ = v_a_4372_;
                                        v___y_4380_ = v_a_4373_;
                                        v___y_4381_ = v_a_4374_;
                                        v___y_4382_ = v_a_4375_;
                                        v___y_4383_ = v_a_4376_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_val_4473_);
                                    lean_dec(v_fvarId_4468_);
                                    lean_dec(v_idx_4424_);
                                    lean_del_object(v___x_4421_);
                                    lean_dec(v_binderName_4388_);
                                    lean_dec(v_fvarId_4387_);
                                    lean_dec_ref(v_k_4371_);
                                    v___y_4379_ = v_a_4372_;
                                    v___y_4380_ = v_a_4373_;
                                    v___y_4381_ = v_a_4374_;
                                    v___y_4382_ = v_a_4375_;
                                    v___y_4383_ = v_a_4376_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4472_);
                                lean_dec(v_fvarId_4468_);
                                lean_dec(v_idx_4424_);
                                lean_del_object(v___x_4421_);
                                lean_dec(v_binderName_4388_);
                                lean_dec(v_fvarId_4387_);
                                lean_dec_ref(v_k_4371_);
                                v___y_4379_ = v_a_4372_;
                                v___y_4380_ = v_a_4373_;
                                v___y_4381_ = v_a_4374_;
                                v___y_4382_ = v_a_4375_;
                                v___y_4383_ = v_a_4376_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_idx_4424_);
                            lean_dec(v_typeName_4423_);
                            lean_del_object(v___x_4421_);
                            lean_dec(v_binderName_4388_);
                            v___x_4500_ = lean_st_ref_take(v_a_4372_);
                            v_subst_4501_ = lean_ctor_get(v___x_4500_, 0);
                            v_jpParamMask_4502_ = lean_ctor_get(v___x_4500_, 1);
                            v_isSharedCheck_4513_ = (!lean_is_exclusive(v___x_4500_)) as u8;
                            if v_isSharedCheck_4513_ == 0 {
                                v___x_4504_ = v___x_4500_;
                                v_isShared_4505_ = v_isSharedCheck_4513_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_jpParamMask_4502_);
                                lean_inc(v_subst_4501_);
                                lean_dec(v___x_4500_);
                                v___x_4504_ = lean_box(0);
                                v_isShared_4505_ = v_isSharedCheck_4513_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_struct_4425_);
                    lean_dec(v_idx_4424_);
                    lean_dec(v_typeName_4423_);
                    lean_del_object(v___x_4421_);
                    lean_dec(v_binderName_4388_);
                    lean_dec(v_fvarId_4387_);
                    lean_dec_ref(v_k_4371_);
                    v_a_4514_ = lean_ctor_get(v___x_4426_, 0);
                    v_isSharedCheck_4521_ = (!lean_is_exclusive(v___x_4426_)) as u8;
                    if v_isSharedCheck_4521_ == 0 {
                        v___x_4516_ = v___x_4426_;
                        v_isShared_4517_ = v_isSharedCheck_4521_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_4514_);
                        lean_dec(v___x_4426_);
                        v___x_4516_ = lean_box(0);
                        v_isShared_4517_ = v_isSharedCheck_4521_;
                        state = 19;
                        continue;
                    }
                }
            }
            8 => {
                v_fieldIdx_4432_ = lean_ctor_get(v_val_4428_, 2);
                lean_inc(v_fieldIdx_4432_);
                lean_dec(v_val_4428_);
                v___x_4433_ = lean_nat_dec_eq(v_fieldIdx_4432_, v_idx_4424_);
                lean_dec(v_idx_4424_);
                lean_dec(v_fieldIdx_4432_);
                if v___x_4433_ == 0 {
                    lean_del_object(v___x_4430_);
                    lean_dec(v_struct_4425_);
                    v___x_4434_ = lean_st_ref_take(v_a_4372_);
                    v_subst_4435_ = lean_ctor_get(v___x_4434_, 0);
                    v_jpParamMask_4436_ = lean_ctor_get(v___x_4434_, 1);
                    v_isSharedCheck_4447_ = (!lean_is_exclusive(v___x_4434_)) as u8;
                    if v_isSharedCheck_4447_ == 0 {
                        v___x_4438_ = v___x_4434_;
                        v_isShared_4439_ = v_isSharedCheck_4447_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_jpParamMask_4436_);
                        lean_inc(v_subst_4435_);
                        lean_dec(v___x_4434_);
                        v___x_4438_ = lean_box(0);
                        v_isShared_4439_ = v_isSharedCheck_4447_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_4448_ = lean_st_ref_take(v_a_4372_);
                    v_subst_4449_ = lean_ctor_get(v___x_4448_, 0);
                    v_jpParamMask_4450_ = lean_ctor_get(v___x_4448_, 1);
                    v_isSharedCheck_4463_ = (!lean_is_exclusive(v___x_4448_)) as u8;
                    if v_isSharedCheck_4463_ == 0 {
                        v___x_4452_ = v___x_4448_;
                        v_isShared_4453_ = v_isSharedCheck_4463_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_jpParamMask_4450_);
                        lean_inc(v_subst_4449_);
                        lean_dec(v___x_4448_);
                        v___x_4452_ = lean_box(0);
                        v_isShared_4453_ = v_isSharedCheck_4463_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_4440_ = lean_box(0);
                v___x_4441_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_4435_, v_fvarId_4387_, v___x_4440_);
                if v_isShared_4439_ == 0 {
                    lean_ctor_set(v___x_4438_, 0, v___x_4441_);
                    v___x_4443_ = v___x_4438_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4441_);
                    lean_ctor_set(v_reuseFailAlloc_4446_, 1, v_jpParamMask_4436_);
                    v___x_4443_ = v_reuseFailAlloc_4446_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4444_ = lean_st_ref_set(v_a_4372_, v___x_4443_);
                v___x_4445_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_k_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_,
                    );
                return v___x_4445_;
            }
            11 => {
                if v_isShared_4431_ == 0 {
                    lean_ctor_set(v___x_4430_, 0, v_struct_4425_);
                    v___x_4455_ = v___x_4430_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_struct_4425_);
                    v___x_4455_ = v_reuseFailAlloc_4462_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4456_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_4449_, v_fvarId_4387_, v___x_4455_);
                if v_isShared_4453_ == 0 {
                    lean_ctor_set(v___x_4452_, 0, v___x_4456_);
                    v___x_4458_ = v___x_4452_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4456_);
                    lean_ctor_set(v_reuseFailAlloc_4461_, 1, v_jpParamMask_4450_);
                    v___x_4458_ = v_reuseFailAlloc_4461_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4459_ = lean_st_ref_set(v_a_4372_, v___x_4458_);
                v___x_4460_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_k_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_,
                    );
                return v___x_4460_;
            }
            14 => {
                v___x_4490_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_4371_, v___x_4489_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4490_;
            }
            15 => {
                if v_isShared_4495_ == 0 {
                    v___x_4497_ = v___x_4494_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
                    v___x_4497_ = v_reuseFailAlloc_4498_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4497_;
            }
            17 => {
                v___x_4506_ = lean_box(0);
                v___x_4507_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_4501_, v_fvarId_4387_, v___x_4506_);
                if v_isShared_4505_ == 0 {
                    lean_ctor_set(v___x_4504_, 0, v___x_4507_);
                    v___x_4509_ = v___x_4504_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4507_);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_jpParamMask_4502_);
                    v___x_4509_ = v_reuseFailAlloc_4512_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4510_ = lean_st_ref_set(v_a_4372_, v___x_4509_);
                v___x_4511_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_k_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_,
                    );
                return v___x_4511_;
            }
            19 => {
                if v_isShared_4517_ == 0 {
                    v___x_4519_ = v___x_4516_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
                    v___x_4519_ = v_reuseFailAlloc_4520_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4519_;
            }
            21 => {
                v___x_4556_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6;
                v___x_4557_ = l_Lean_Name_toString(v_declName_4527_, v___x_4396_);
                if v_isShared_4555_ == 0 {
                    lean_ctor_set_tag(v___x_4554_, 3);
                    lean_ctor_set(v___x_4554_, 0, v___x_4557_);
                    v___x_4559_ = v___x_4554_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4567_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4557_);
                    v___x_4559_ = v_reuseFailAlloc_4567_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_4394_ == 0 {
                    lean_ctor_set_tag(v___x_4393_, 5);
                    lean_ctor_set(v___x_4393_, 1, v___x_4559_);
                    lean_ctor_set(v___x_4393_, 0, v___x_4556_);
                    v___x_4561_ = v___x_4393_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4566_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4556_);
                    lean_ctor_set(v_reuseFailAlloc_4566_, 1, v___x_4559_);
                    v___x_4561_ = v_reuseFailAlloc_4566_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_4562_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8;
                v___x_4563_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4563_, 0, v___x_4561_);
                lean_ctor_set(v___x_4563_, 1, v___x_4562_);
                v___x_4564_ = l_Lean_MessageData_ofFormat(v___x_4563_);
                v___x_4565_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_4564_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4565_;
            }
            24 => {
                v___x_4573_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6;
                v___x_4574_ = l_Lean_Name_toString(v_declName_4527_, v___x_4396_);
                if v_isShared_4572_ == 0 {
                    lean_ctor_set_tag(v___x_4571_, 3);
                    lean_ctor_set(v___x_4571_, 0, v___x_4574_);
                    v___x_4576_ = v___x_4571_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4584_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4574_);
                    v___x_4576_ = v_reuseFailAlloc_4584_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_4394_ == 0 {
                    lean_ctor_set_tag(v___x_4393_, 5);
                    lean_ctor_set(v___x_4393_, 1, v___x_4576_);
                    lean_ctor_set(v___x_4393_, 0, v___x_4573_);
                    v___x_4578_ = v___x_4393_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4573_);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 1, v___x_4576_);
                    v___x_4578_ = v_reuseFailAlloc_4583_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4579_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8;
                v___x_4580_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4580_, 0, v___x_4578_);
                lean_ctor_set(v___x_4580_, 1, v___x_4579_);
                v___x_4581_ = l_Lean_MessageData_ofFormat(v___x_4580_);
                v___x_4582_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_4581_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4582_;
            }
            27 => {
                v___x_4590_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6;
                v___x_4591_ = l_Lean_Name_toString(v_declName_4527_, v___x_4396_);
                if v_isShared_4589_ == 0 {
                    lean_ctor_set_tag(v___x_4588_, 3);
                    lean_ctor_set(v___x_4588_, 0, v___x_4591_);
                    v___x_4593_ = v___x_4588_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4601_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4591_);
                    v___x_4593_ = v_reuseFailAlloc_4601_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_4394_ == 0 {
                    lean_ctor_set_tag(v___x_4393_, 5);
                    lean_ctor_set(v___x_4393_, 1, v___x_4593_);
                    lean_ctor_set(v___x_4393_, 0, v___x_4590_);
                    v___x_4595_ = v___x_4393_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4600_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4590_);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 1, v___x_4593_);
                    v___x_4595_ = v_reuseFailAlloc_4600_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_4596_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8;
                v___x_4597_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4597_, 0, v___x_4595_);
                lean_ctor_set(v___x_4597_, 1, v___x_4596_);
                v___x_4598_ = l_Lean_MessageData_ofFormat(v___x_4597_);
                v___x_4599_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_4598_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4599_;
            }
            30 => {
                v___x_4607_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6;
                v___x_4608_ = l_Lean_Name_toString(v_declName_4527_, v___x_4396_);
                if v_isShared_4606_ == 0 {
                    lean_ctor_set_tag(v___x_4605_, 3);
                    lean_ctor_set(v___x_4605_, 0, v___x_4608_);
                    v___x_4610_ = v___x_4605_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4618_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4608_);
                    v___x_4610_ = v_reuseFailAlloc_4618_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_4394_ == 0 {
                    lean_ctor_set_tag(v___x_4393_, 5);
                    lean_ctor_set(v___x_4393_, 1, v___x_4610_);
                    lean_ctor_set(v___x_4393_, 0, v___x_4607_);
                    v___x_4612_ = v___x_4393_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4607_);
                    lean_ctor_set(v_reuseFailAlloc_4617_, 1, v___x_4610_);
                    v___x_4612_ = v_reuseFailAlloc_4617_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_4613_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8;
                v___x_4614_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4614_, 0, v___x_4612_);
                lean_ctor_set(v___x_4614_, 1, v___x_4613_);
                v___x_4615_ = l_Lean_MessageData_ofFormat(v___x_4614_);
                v___x_4616_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_4615_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4616_;
            }
            33 => {
                v_induct_4625_ = lean_ctor_get(v_val_4621_, 1);
                lean_inc_n(v_induct_4625_, 2);
                v_cidx_4626_ = lean_ctor_get(v_val_4621_, 2);
                lean_inc(v_cidx_4626_);
                v_numParams_4627_ = lean_ctor_get(v_val_4621_, 3);
                lean_inc(v_numParams_4627_);
                lean_dec_ref(v_val_4621_);
                v___x_4628_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(
                    v_induct_4625_,
                    v_a_4375_,
                    v_a_4376_,
                );
                if lean_obj_tag(v___x_4628_) == 0 {
                    v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
                    lean_inc(v_a_4629_);
                    lean_dec_ref_known(v___x_4628_, 1);
                    if lean_obj_tag(v_a_4629_) == 1 {
                        lean_inc(v_fvarId_4387_);
                        lean_dec(v_numParams_4627_);
                        lean_dec(v_cidx_4626_);
                        lean_dec(v_induct_4625_);
                        lean_del_object(v___x_4623_);
                        lean_dec(v_a_4532_);
                        lean_dec(v_declName_4527_);
                        lean_del_object(v___x_4393_);
                        lean_dec_ref(v_decl_4370_);
                        v_val_4630_ = lean_ctor_get(v_a_4629_, 0);
                        lean_inc(v_val_4630_);
                        lean_dec_ref_known(v_a_4629_, 1);
                        v___x_4631_ = lean_st_ref_take(v_a_4372_);
                        v_numParams_4632_ = lean_ctor_get(v_val_4630_, 1);
                        lean_inc(v_numParams_4632_);
                        v_fieldIdx_4633_ = lean_ctor_get(v_val_4630_, 2);
                        lean_inc(v_fieldIdx_4633_);
                        lean_dec(v_val_4630_);
                        v_subst_4634_ = lean_ctor_get(v___x_4631_, 0);
                        v_jpParamMask_4635_ = lean_ctor_get(v___x_4631_, 1);
                        v_isSharedCheck_4648_ = (!lean_is_exclusive(v___x_4631_)) as u8;
                        if v_isSharedCheck_4648_ == 0 {
                            v___x_4637_ = v___x_4631_;
                            v_isShared_4638_ = v_isSharedCheck_4648_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_jpParamMask_4635_);
                            lean_inc(v_subst_4634_);
                            lean_dec(v___x_4631_);
                            v___x_4637_ = lean_box(0);
                            v_isShared_4638_ = v_isSharedCheck_4648_;
                            state = 34;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4629_);
                        lean_dec_ref(v_args_4528_);
                        v___x_4649_ = l_Lean_Compiler_LCNF_nameToImpureType(
                            v_induct_4625_,
                            v_a_4375_,
                            v_a_4376_,
                        );
                        if lean_obj_tag(v___x_4649_) == 0 {
                            v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
                            lean_inc(v_a_4650_);
                            lean_dec_ref_known(v___x_4649_, 1);
                            v___x_4651_ =
                                l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_4650_);
                            if v___x_4651_ == 0 {
                                lean_dec(v_a_4650_);
                                lean_dec(v_cidx_4626_);
                                lean_del_object(v___x_4623_);
                                v___x_4652_ = l_Lean_Compiler_LCNF_getCtorLayout(
                                    v_declName_4527_,
                                    v_a_4375_,
                                    v_a_4376_,
                                );
                                if lean_obj_tag(v___x_4652_) == 0 {
                                    v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
                                    v_isSharedCheck_4715_ = (!lean_is_exclusive(v___x_4652_)) as u8;
                                    if v_isSharedCheck_4715_ == 0 {
                                        v___x_4655_ = v___x_4652_;
                                        v_isShared_4656_ = v_isSharedCheck_4715_;
                                        state = 36;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4653_);
                                        lean_dec(v___x_4652_);
                                        v___x_4655_ = lean_box(0);
                                        v_isShared_4656_ = v_isSharedCheck_4715_;
                                        state = 36;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_numParams_4627_);
                                    lean_dec(v_a_4532_);
                                    lean_del_object(v___x_4393_);
                                    lean_dec_ref(v_k_4371_);
                                    lean_dec_ref(v_decl_4370_);
                                    v_a_4716_ = lean_ctor_get(v___x_4652_, 0);
                                    v_isSharedCheck_4723_ = (!lean_is_exclusive(v___x_4652_)) as u8;
                                    if v_isSharedCheck_4723_ == 0 {
                                        v___x_4718_ = v___x_4652_;
                                        v_isShared_4719_ = v_isSharedCheck_4723_;
                                        state = 48;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4716_);
                                        lean_dec(v___x_4652_);
                                        v___x_4718_ = lean_box(0);
                                        v_isShared_4719_ = v_isSharedCheck_4723_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v_binderName_4388_);
                                lean_inc(v_fvarId_4387_);
                                lean_dec(v_numParams_4627_);
                                lean_dec(v_a_4532_);
                                lean_dec(v_declName_4527_);
                                lean_del_object(v___x_4393_);
                                v_isSharedCheck_4735_ = (!lean_is_exclusive(v_decl_4370_)) as u8;
                                if v_isSharedCheck_4735_ == 0 {
                                    v_unused_4736_ = lean_ctor_get(v_decl_4370_, 3);
                                    lean_dec(v_unused_4736_);
                                    v_unused_4737_ = lean_ctor_get(v_decl_4370_, 2);
                                    lean_dec(v_unused_4737_);
                                    v_unused_4738_ = lean_ctor_get(v_decl_4370_, 1);
                                    lean_dec(v_unused_4738_);
                                    v_unused_4739_ = lean_ctor_get(v_decl_4370_, 0);
                                    lean_dec(v_unused_4739_);
                                    v___x_4725_ = v_decl_4370_;
                                    v_isShared_4726_ = v_isSharedCheck_4735_;
                                    state = 50;
                                    continue;
                                } else {
                                    lean_dec(v_decl_4370_);
                                    v___x_4725_ = lean_box(0);
                                    v_isShared_4726_ = v_isSharedCheck_4735_;
                                    state = 50;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_numParams_4627_);
                            lean_dec(v_cidx_4626_);
                            lean_del_object(v___x_4623_);
                            lean_dec(v_a_4532_);
                            lean_dec(v_declName_4527_);
                            lean_del_object(v___x_4393_);
                            lean_dec_ref(v_k_4371_);
                            lean_dec_ref(v_decl_4370_);
                            v_a_4740_ = lean_ctor_get(v___x_4649_, 0);
                            v_isSharedCheck_4747_ = (!lean_is_exclusive(v___x_4649_)) as u8;
                            if v_isSharedCheck_4747_ == 0 {
                                v___x_4742_ = v___x_4649_;
                                v_isShared_4743_ = v_isSharedCheck_4747_;
                                state = 53;
                                continue;
                            } else {
                                lean_inc(v_a_4740_);
                                lean_dec(v___x_4649_);
                                v___x_4742_ = lean_box(0);
                                v_isShared_4743_ = v_isSharedCheck_4747_;
                                state = 53;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_numParams_4627_);
                    lean_dec(v_cidx_4626_);
                    lean_dec(v_induct_4625_);
                    lean_del_object(v___x_4623_);
                    lean_dec(v_a_4532_);
                    lean_dec_ref(v_args_4528_);
                    lean_dec(v_declName_4527_);
                    lean_del_object(v___x_4393_);
                    lean_dec_ref(v_k_4371_);
                    lean_dec_ref(v_decl_4370_);
                    v_a_4748_ = lean_ctor_get(v___x_4628_, 0);
                    v_isSharedCheck_4755_ = (!lean_is_exclusive(v___x_4628_)) as u8;
                    if v_isSharedCheck_4755_ == 0 {
                        v___x_4750_ = v___x_4628_;
                        v_isShared_4751_ = v_isSharedCheck_4755_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_a_4748_);
                        lean_dec(v___x_4628_);
                        v___x_4750_ = lean_box(0);
                        v_isShared_4751_ = v_isSharedCheck_4755_;
                        state = 55;
                        continue;
                    }
                }
            }
            34 => {
                v___x_4639_ = lean_box(0);
                v___x_4640_ = lean_nat_add(v_numParams_4632_, v_fieldIdx_4633_);
                lean_dec(v_fieldIdx_4633_);
                lean_dec(v_numParams_4632_);
                v___x_4641_ = lean_array_get(v___x_4639_, v_args_4528_, v___x_4640_);
                lean_dec(v___x_4640_);
                lean_dec_ref(v_args_4528_);
                v___x_4642_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_4634_, v_fvarId_4387_, v___x_4641_);
                if v_isShared_4638_ == 0 {
                    lean_ctor_set(v___x_4637_, 0, v___x_4642_);
                    v___x_4644_ = v___x_4637_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4642_);
                    lean_ctor_set(v_reuseFailAlloc_4647_, 1, v_jpParamMask_4635_);
                    v___x_4644_ = v_reuseFailAlloc_4647_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_4645_ = lean_st_ref_set(v_a_4372_, v___x_4644_);
                v___x_4646_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_k_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_,
                    );
                return v___x_4646_;
            }
            36 => {
                v_ctorInfo_4662_ = lean_ctor_get(v_a_4653_, 0);
                v_fieldInfo_4663_ = lean_ctor_get(v_a_4653_, 1);
                v_isSharedCheck_4714_ = (!lean_is_exclusive(v_a_4653_)) as u8;
                if v_isSharedCheck_4714_ == 0 {
                    v___x_4665_ = v_a_4653_;
                    v_isShared_4666_ = v_isSharedCheck_4714_;
                    state = 39;
                    continue;
                } else {
                    lean_inc(v_fieldInfo_4663_);
                    lean_inc(v_ctorInfo_4662_);
                    lean_dec(v_a_4653_);
                    v___x_4665_ = lean_box(0);
                    v_isShared_4666_ = v_isSharedCheck_4714_;
                    state = 39;
                    continue;
                }
            }
            37 => {
                v___x_4658_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
                if v_isShared_4656_ == 0 {
                    lean_ctor_set(v___x_4655_, 0, v___x_4658_);
                    v___x_4660_ = v___x_4655_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
                    v___x_4660_ = v_reuseFailAlloc_4661_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4660_;
            }
            39 => {
                v___x_4667_ = lean_array_get_size(v_a_4532_);
                v___x_4668_ = l_Array_extract___redArg(v_a_4532_, v_numParams_4627_, v___x_4667_);
                lean_dec(v_a_4532_);
                v___x_4669_ = lean_array_get_size(v___x_4668_);
                v___x_4670_ = lean_array_get_size(v_fieldInfo_4663_);
                v___x_4671_ = lean_nat_dec_eq(v___x_4669_, v___x_4670_);
                if v___x_4671_ == 0 {
                    lean_dec_ref(v___x_4668_);
                    lean_del_object(v___x_4665_);
                    lean_dec_ref(v_fieldInfo_4663_);
                    lean_dec_ref(v_ctorInfo_4662_);
                    lean_del_object(v___x_4393_);
                    lean_dec_ref(v_k_4371_);
                    lean_dec_ref(v_decl_4370_);
                    state = 37;
                    continue;
                } else {
                    if v___x_4651_ == 0 {
                        lean_del_object(v___x_4655_);
                        v___x_4672_ = lean_unsigned_to_nat(0);
                        v___x_4673_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4;
                        v___x_4674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_4670_, v_fieldInfo_4663_, v___x_4668_, v___x_4672_, v___x_4673_);
                        if lean_obj_tag(v___x_4674_) == 0 {
                            v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
                            lean_inc(v_a_4675_);
                            lean_dec_ref_known(v___x_4674_, 1);
                            v___x_4676_ = lean_st_ref_take(v_a_4374_);
                            v_lctx_4677_ = lean_ctor_get(v___x_4676_, 0);
                            v_nextIdx_4678_ = lean_ctor_get(v___x_4676_, 1);
                            v_isSharedCheck_4705_ = (!lean_is_exclusive(v___x_4676_)) as u8;
                            if v_isSharedCheck_4705_ == 0 {
                                v___x_4680_ = v___x_4676_;
                                v_isShared_4681_ = v_isSharedCheck_4705_;
                                state = 40;
                                continue;
                            } else {
                                lean_inc(v_nextIdx_4678_);
                                lean_inc(v_lctx_4677_);
                                lean_dec(v___x_4676_);
                                v___x_4680_ = lean_box(0);
                                v_isShared_4681_ = v_isSharedCheck_4705_;
                                state = 40;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_4668_);
                            lean_del_object(v___x_4665_);
                            lean_dec_ref(v_fieldInfo_4663_);
                            lean_dec_ref(v_ctorInfo_4662_);
                            lean_del_object(v___x_4393_);
                            lean_dec_ref(v_k_4371_);
                            lean_dec_ref(v_decl_4370_);
                            v_a_4706_ = lean_ctor_get(v___x_4674_, 0);
                            v_isSharedCheck_4713_ = (!lean_is_exclusive(v___x_4674_)) as u8;
                            if v_isSharedCheck_4713_ == 0 {
                                v___x_4708_ = v___x_4674_;
                                v_isShared_4709_ = v_isSharedCheck_4713_;
                                state = 46;
                                continue;
                            } else {
                                lean_inc(v_a_4706_);
                                lean_dec(v___x_4674_);
                                v___x_4708_ = lean_box(0);
                                v_isShared_4709_ = v_isSharedCheck_4713_;
                                state = 46;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_4668_);
                        lean_del_object(v___x_4665_);
                        lean_dec_ref(v_fieldInfo_4663_);
                        lean_dec_ref(v_ctorInfo_4662_);
                        lean_del_object(v___x_4393_);
                        lean_dec_ref(v_k_4371_);
                        lean_dec_ref(v_decl_4370_);
                        state = 37;
                        continue;
                    }
                }
            }
            40 => {
                v___x_4682_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_4662_);
                v___x_4683_ = 1;
                lean_inc_ref(v_ctorInfo_4662_);
                if v_isShared_4666_ == 0 {
                    lean_ctor_set_tag(v___x_4665_, 5);
                    lean_ctor_set(v___x_4665_, 1, v_a_4675_);
                    v___x_4685_ = v___x_4665_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_ctorInfo_4662_);
                    lean_ctor_set(v_reuseFailAlloc_4704_, 1, v_a_4675_);
                    v___x_4685_ = v_reuseFailAlloc_4704_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                lean_inc(v_binderName_4388_);
                lean_inc(v_fvarId_4387_);
                v___x_4686_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4686_, 0, v_fvarId_4387_);
                lean_ctor_set(v___x_4686_, 1, v_binderName_4388_);
                lean_ctor_set(v___x_4686_, 2, v___x_4682_);
                lean_ctor_set(v___x_4686_, 3, v___x_4685_);
                lean_inc_ref(v___x_4686_);
                v___x_4687_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_4683_, v_lctx_4677_, v___x_4686_);
                if v_isShared_4681_ == 0 {
                    lean_ctor_set(v___x_4680_, 0, v___x_4687_);
                    v___x_4689_ = v___x_4680_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4687_);
                    lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_nextIdx_4678_);
                    v___x_4689_ = v_reuseFailAlloc_4703_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v___x_4690_ = lean_st_ref_set(v_a_4374_, v___x_4689_);
                v___x_4691_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_4370_, v_k_4371_, v_ctorInfo_4662_, v_fieldInfo_4663_, v___x_4668_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                lean_dec_ref(v___x_4668_);
                lean_dec_ref(v_fieldInfo_4663_);
                lean_dec_ref(v_ctorInfo_4662_);
                if lean_obj_tag(v___x_4691_) == 0 {
                    v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
                    v_isSharedCheck_4702_ = (!lean_is_exclusive(v___x_4691_)) as u8;
                    if v_isSharedCheck_4702_ == 0 {
                        v___x_4694_ = v___x_4691_;
                        v_isShared_4695_ = v_isSharedCheck_4702_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_a_4692_);
                        lean_dec(v___x_4691_);
                        v___x_4694_ = lean_box(0);
                        v_isShared_4695_ = v_isSharedCheck_4702_;
                        state = 43;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_4686_, 4);
                    lean_del_object(v___x_4393_);
                    return v___x_4691_;
                }
            }
            43 => {
                if v_isShared_4394_ == 0 {
                    lean_ctor_set(v___x_4393_, 1, v_a_4692_);
                    lean_ctor_set(v___x_4393_, 0, v___x_4686_);
                    v___x_4697_ = v___x_4393_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4686_);
                    lean_ctor_set(v_reuseFailAlloc_4701_, 1, v_a_4692_);
                    v___x_4697_ = v_reuseFailAlloc_4701_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_4695_ == 0 {
                    lean_ctor_set(v___x_4694_, 0, v___x_4697_);
                    v___x_4699_ = v___x_4694_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4697_);
                    v___x_4699_ = v_reuseFailAlloc_4700_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4699_;
            }
            46 => {
                if v_isShared_4709_ == 0 {
                    v___x_4711_ = v___x_4708_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
                    v___x_4711_ = v_reuseFailAlloc_4712_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_4711_;
            }
            48 => {
                if v_isShared_4719_ == 0 {
                    v___x_4721_ = v___x_4718_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
                    v___x_4721_ = v_reuseFailAlloc_4722_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4721_;
            }
            50 => {
                v___x_4727_ =
                    l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_4650_, v_cidx_4626_);
                lean_dec(v_cidx_4626_);
                if v_isShared_4624_ == 0 {
                    lean_ctor_set_tag(v___x_4623_, 0);
                    lean_ctor_set(v___x_4623_, 0, v___x_4727_);
                    v___x_4729_ = v___x_4623_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4727_);
                    v___x_4729_ = v_reuseFailAlloc_4734_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_4726_ == 0 {
                    lean_ctor_set(v___x_4725_, 3, v___x_4729_);
                    lean_ctor_set(v___x_4725_, 2, v_a_4650_);
                    v___x_4731_ = v___x_4725_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_fvarId_4387_);
                    lean_ctor_set(v_reuseFailAlloc_4733_, 1, v_binderName_4388_);
                    lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_a_4650_);
                    lean_ctor_set(v_reuseFailAlloc_4733_, 3, v___x_4729_);
                    v___x_4731_ = v_reuseFailAlloc_4733_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_4732_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_4371_, v___x_4731_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4732_;
            }
            53 => {
                if v_isShared_4743_ == 0 {
                    v___x_4745_ = v___x_4742_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
                    v___x_4745_ = v_reuseFailAlloc_4746_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_4745_;
            }
            55 => {
                if v_isShared_4751_ == 0 {
                    v___x_4753_ = v___x_4750_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
                    v___x_4753_ = v_reuseFailAlloc_4754_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_4753_;
            }
            57 => {
                v___x_4760_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11;
                v___x_4761_ = l_Lean_Name_toString(v_declName_4527_, v___x_4396_);
                if v_isShared_4759_ == 0 {
                    lean_ctor_set_tag(v___x_4758_, 3);
                    lean_ctor_set(v___x_4758_, 0, v___x_4761_);
                    v___x_4763_ = v___x_4758_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_4771_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4761_);
                    v___x_4763_ = v_reuseFailAlloc_4771_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                if v_isShared_4394_ == 0 {
                    lean_ctor_set_tag(v___x_4393_, 5);
                    lean_ctor_set(v___x_4393_, 1, v___x_4763_);
                    lean_ctor_set(v___x_4393_, 0, v___x_4760_);
                    v___x_4765_ = v___x_4393_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_4770_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4760_);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 1, v___x_4763_);
                    v___x_4765_ = v_reuseFailAlloc_4770_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                v___x_4766_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13;
                v___x_4767_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4767_, 0, v___x_4765_);
                lean_ctor_set(v___x_4767_, 1, v___x_4766_);
                v___x_4768_ = l_Lean_MessageData_ofFormat(v___x_4767_);
                v___x_4769_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_4768_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4769_;
            }
            60 => {
                if v_isShared_4778_ == 0 {
                    v___x_4780_ = v___x_4777_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
                    v___x_4780_ = v_reuseFailAlloc_4781_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_4780_;
            }
            62 => {
                if v_isShared_4786_ == 0 {
                    v___x_4788_ = v___x_4785_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
                    v___x_4788_ = v_reuseFailAlloc_4789_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_4788_;
            }
            64 => {
                if v_isShared_4794_ == 0 {
                    v___x_4796_ = v___x_4793_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
                    v___x_4796_ = v_reuseFailAlloc_4797_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_4796_;
            }
            66 => {
                v_fvarId_4802_ = lean_ctor_get(v___x_4397_, 0);
                v_args_4803_ = lean_ctor_get(v___x_4397_, 1);
                v_isSharedCheck_4837_ = (!lean_is_exclusive(v___x_4397_)) as u8;
                if v_isSharedCheck_4837_ == 0 {
                    v___x_4805_ = v___x_4397_;
                    v_isShared_4806_ = v_isSharedCheck_4837_;
                    state = 67;
                    continue;
                } else {
                    lean_inc(v_args_4803_);
                    lean_inc(v_fvarId_4802_);
                    lean_dec(v___x_4397_);
                    v___x_4805_ = lean_box(0);
                    v_isShared_4806_ = v_isSharedCheck_4837_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v_sz_4807_ = lean_array_size(v_args_4803_);
                v___x_4808_ = 0usize;
                v___x_4809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_4807_, v___x_4808_, v_args_4803_, v_a_4372_);
                if lean_obj_tag(v___x_4809_) == 0 {
                    v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
                    lean_inc(v_a_4810_);
                    lean_dec_ref_known(v___x_4809_, 1);
                    v___x_4811_ =
                        l_Lean_Compiler_LCNF_toImpureType(v_type_4389_, v_a_4375_, v_a_4376_);
                    if lean_obj_tag(v___x_4811_) == 0 {
                        v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
                        lean_inc(v_a_4812_);
                        lean_dec_ref_known(v___x_4811_, 1);
                        v___x_4813_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_4812_);
                        lean_dec(v_a_4812_);
                        if v_isShared_4806_ == 0 {
                            lean_ctor_set(v___x_4805_, 1, v_a_4810_);
                            v___x_4815_ = v___x_4805_;
                            state = 68;
                            continue;
                        } else {
                            v_reuseFailAlloc_4820_ = lean_alloc_ctor(4, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_fvarId_4802_);
                            lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_a_4810_);
                            v___x_4815_ = v_reuseFailAlloc_4820_;
                            state = 68;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4810_);
                        lean_del_object(v___x_4805_);
                        lean_dec(v_fvarId_4802_);
                        lean_del_object(v___x_4800_);
                        lean_dec(v_binderName_4388_);
                        lean_dec(v_fvarId_4387_);
                        lean_dec_ref(v_k_4371_);
                        v_a_4821_ = lean_ctor_get(v___x_4811_, 0);
                        v_isSharedCheck_4828_ = (!lean_is_exclusive(v___x_4811_)) as u8;
                        if v_isSharedCheck_4828_ == 0 {
                            v___x_4823_ = v___x_4811_;
                            v_isShared_4824_ = v_isSharedCheck_4828_;
                            state = 70;
                            continue;
                        } else {
                            lean_inc(v_a_4821_);
                            lean_dec(v___x_4811_);
                            v___x_4823_ = lean_box(0);
                            v_isShared_4824_ = v_isSharedCheck_4828_;
                            state = 70;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4805_);
                    lean_dec(v_fvarId_4802_);
                    lean_del_object(v___x_4800_);
                    lean_dec_ref(v_type_4389_);
                    lean_dec(v_binderName_4388_);
                    lean_dec(v_fvarId_4387_);
                    lean_dec_ref(v_k_4371_);
                    v_a_4829_ = lean_ctor_get(v___x_4809_, 0);
                    v_isSharedCheck_4836_ = (!lean_is_exclusive(v___x_4809_)) as u8;
                    if v_isSharedCheck_4836_ == 0 {
                        v___x_4831_ = v___x_4809_;
                        v_isShared_4832_ = v_isSharedCheck_4836_;
                        state = 72;
                        continue;
                    } else {
                        lean_inc(v_a_4829_);
                        lean_dec(v___x_4809_);
                        v___x_4831_ = lean_box(0);
                        v_isShared_4832_ = v_isSharedCheck_4836_;
                        state = 72;
                        continue;
                    }
                }
            }
            68 => {
                if v_isShared_4801_ == 0 {
                    lean_ctor_set(v___x_4800_, 3, v___x_4815_);
                    lean_ctor_set(v___x_4800_, 2, v___x_4813_);
                    v___x_4817_ = v___x_4800_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_fvarId_4387_);
                    lean_ctor_set(v_reuseFailAlloc_4819_, 1, v_binderName_4388_);
                    lean_ctor_set(v_reuseFailAlloc_4819_, 2, v___x_4813_);
                    lean_ctor_set(v_reuseFailAlloc_4819_, 3, v___x_4815_);
                    v___x_4817_ = v_reuseFailAlloc_4819_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_4818_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_4371_, v___x_4817_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
                return v___x_4818_;
            }
            70 => {
                if v_isShared_4824_ == 0 {
                    v___x_4826_ = v___x_4823_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
                    v___x_4826_ = v_reuseFailAlloc_4827_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_4826_;
            }
            72 => {
                if v_isShared_4832_ == 0 {
                    v___x_4834_ = v___x_4831_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
                    v___x_4834_ = v_reuseFailAlloc_4835_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_4834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2()
-> *mut LeanObject {
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    v___x_4847_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1;
    v___x_4848_ = lean_unsigned_to_nat(15);
    v___x_4849_ = lean_unsigned_to_nat(272);
    v___x_4850_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0;
    v___x_4851_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4852_ = l_mkPanicMessageWithDecl(
        v___x_4851_,
        v___x_4850_,
        v___x_4849_,
        v___x_4848_,
        v___x_4847_,
    );
    return v___x_4852_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6()
-> *mut LeanObject {
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    v___x_4856_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5;
    v___x_4857_ = lean_unsigned_to_nat(6);
    v___x_4858_ = lean_unsigned_to_nat(251);
    v___x_4859_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0;
    v___x_4860_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4861_ = l_mkPanicMessageWithDecl(
        v___x_4860_,
        v___x_4859_,
        v___x_4858_,
        v___x_4857_,
        v___x_4856_,
    );
    return v___x_4861_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7()
-> *mut LeanObject {
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    v___x_4862_ = 0;
    v___x_4863_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_4862_);
    return v___x_4863_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9()
-> *mut LeanObject {
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    v___x_4865_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8;
    v___x_4866_ = lean_unsigned_to_nat(6);
    v___x_4867_ = lean_unsigned_to_nat(253);
    v___x_4868_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0;
    v___x_4869_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4870_ = l_mkPanicMessageWithDecl(
        v___x_4869_,
        v___x_4868_,
        v___x_4867_,
        v___x_4866_,
        v___x_4865_,
    );
    return v___x_4870_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11()
-> *mut LeanObject {
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    v___x_4872_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10;
    v___x_4873_ = lean_unsigned_to_nat(6);
    v___x_4874_ = lean_unsigned_to_nat(254);
    v___x_4875_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0;
    v___x_4876_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4877_ = l_mkPanicMessageWithDecl(
        v___x_4876_,
        v___x_4875_,
        v___x_4874_,
        v___x_4873_,
        v___x_4872_,
    );
    return v___x_4877_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13()
-> *mut LeanObject {
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    v___x_4879_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12;
    v___x_4880_ = lean_unsigned_to_nat(45);
    v___x_4881_ = lean_unsigned_to_nat(252);
    v___x_4882_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0;
    v___x_4883_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4884_ = l_mkPanicMessageWithDecl(
        v___x_4883_,
        v___x_4882_,
        v___x_4881_,
        v___x_4880_,
        v___x_4879_,
    );
    return v___x_4884_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2()
-> *mut LeanObject {
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    v___x_4887_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1;
    v___x_4888_ = lean_unsigned_to_nat(18);
    v___x_4889_ = lean_unsigned_to_nat(293);
    v___x_4890_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0;
    v___x_4891_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0;
    v___x_4892_ = l_mkPanicMessageWithDecl(
        v___x_4891_,
        v___x_4890_,
        v___x_4889_,
        v___x_4888_,
        v___x_4887_,
    );
    return v___x_4892_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(
    mut v_discr_4893_: *mut LeanObject,
    mut v_k_4894_: *mut LeanObject,
    mut v_ctorInfo_4895_: *mut LeanObject,
    mut v_params_4896_: *mut LeanObject,
    mut v_fields_4897_: *mut LeanObject,
    mut v_i_4898_: *mut LeanObject,
    mut v_a_4899_: *mut LeanObject,
    mut v_a_4900_: *mut LeanObject,
    mut v_a_4901_: *mut LeanObject,
    mut v_a_4902_: *mut LeanObject,
    mut v_a_4903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4937_: u8 = 0;
    let mut v_snd_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4949_: u8 = 0;
    let mut v___x_4950_: u8 = 0;
    let mut v_decl_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4962_: u8 = 0;
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4969_: u8 = 0;
    let mut v_reuseFailAlloc_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4971_: u8 = 0;
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut v_unused_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: u8 = 0;
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: u8 = 0;
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4981_ = lean_array_get_size(v_params_4896_);
                v___x_4982_ = lean_nat_dec_lt(v_i_4898_, v___x_4981_);
                if v___x_4982_ == 0 {
                    v___x_4983_ = lean_box(0);
                    v___y_4975_ = v___x_4983_;
                    state = 11;
                    continue;
                } else {
                    v___x_4984_ = lean_array_fget_borrowed(v_params_4896_, v_i_4898_);
                    lean_inc(v___x_4984_);
                    v___x_4985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4985_, 0, v___x_4984_);
                    v___y_4975_ = v___x_4985_;
                    state = 11;
                    continue;
                }
            }
            1 => {
                v___x_4911_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
                v___x_4912_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_4911_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_);
                return v___x_4912_;
            }
            2 => {
                if lean_obj_tag(v___y_4914_) == 0 {
                    lean_dec(v_i_4898_);
                    lean_dec(v_discr_4893_);
                    if lean_obj_tag(v___y_4915_) == 0 {
                        v___x_4916_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_4894_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
                        return v___x_4916_;
                    } else {
                        lean_dec(v___y_4915_);
                        lean_dec_ref(v_k_4894_);
                        v___y_4906_ = v_a_4899_;
                        v___y_4907_ = v_a_4900_;
                        v___y_4908_ = v_a_4901_;
                        v___y_4909_ = v_a_4902_;
                        v___y_4910_ = v_a_4903_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___y_4915_) == 1 {
                        v_val_4917_ = lean_ctor_get(v___y_4914_, 0);
                        lean_inc(v_val_4917_);
                        lean_dec_ref_known(v___y_4914_, 1);
                        v_val_4918_ = lean_ctor_get(v___y_4915_, 0);
                        lean_inc(v_val_4918_);
                        lean_dec_ref_known(v___y_4915_, 1);
                        lean_inc(v_discr_4893_);
                        v___x_4919_ =
                            l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(
                                v_discr_4893_,
                                v_ctorInfo_4895_,
                                v_val_4918_,
                            );
                        v_fst_4920_ = lean_ctor_get(v___x_4919_, 0);
                        lean_inc(v_fst_4920_);
                        if lean_obj_tag(v_fst_4920_) == 1 {
                            lean_dec_ref(v___x_4919_);
                            v___x_4921_ = lean_st_ref_take(v_a_4899_);
                            v_fvarId_4922_ = lean_ctor_get(v_val_4917_, 0);
                            lean_inc(v_fvarId_4922_);
                            lean_dec(v_val_4917_);
                            v_subst_4923_ = lean_ctor_get(v___x_4921_, 0);
                            v_jpParamMask_4924_ = lean_ctor_get(v___x_4921_, 1);
                            v_isSharedCheck_4937_ = (!lean_is_exclusive(v___x_4921_)) as u8;
                            if v_isSharedCheck_4937_ == 0 {
                                v___x_4926_ = v___x_4921_;
                                v_isShared_4927_ = v_isSharedCheck_4937_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_jpParamMask_4924_);
                                lean_inc(v_subst_4923_);
                                lean_dec(v___x_4921_);
                                v___x_4926_ = lean_box(0);
                                v_isShared_4927_ = v_isSharedCheck_4937_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_snd_4938_ = lean_ctor_get(v___x_4919_, 1);
                            v_isSharedCheck_4972_ = (!lean_is_exclusive(v___x_4919_)) as u8;
                            if v_isSharedCheck_4972_ == 0 {
                                v_unused_4973_ = lean_ctor_get(v___x_4919_, 0);
                                lean_dec(v_unused_4973_);
                                v___x_4940_ = v___x_4919_;
                                v_isShared_4941_ = v_isSharedCheck_4972_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_snd_4938_);
                                lean_dec(v___x_4919_);
                                v___x_4940_ = lean_box(0);
                                v_isShared_4941_ = v_isSharedCheck_4972_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___y_4914_, 1);
                        lean_dec(v___y_4915_);
                        lean_dec(v_i_4898_);
                        lean_dec_ref(v_k_4894_);
                        lean_dec(v_discr_4893_);
                        v___y_4906_ = v_a_4899_;
                        v___y_4907_ = v_a_4900_;
                        v___y_4908_ = v_a_4901_;
                        v___y_4909_ = v_a_4902_;
                        v___y_4910_ = v_a_4903_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4928_ = lean_box(0);
                v___x_4929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_4923_, v_fvarId_4922_, v___x_4928_);
                if v_isShared_4927_ == 0 {
                    lean_ctor_set(v___x_4926_, 0, v___x_4929_);
                    v___x_4931_ = v___x_4926_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4929_);
                    lean_ctor_set(v_reuseFailAlloc_4936_, 1, v_jpParamMask_4924_);
                    v___x_4931_ = v_reuseFailAlloc_4936_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4932_ = lean_st_ref_set(v_a_4899_, v___x_4931_);
                v___x_4933_ = lean_unsigned_to_nat(1);
                v___x_4934_ = lean_nat_add(v_i_4898_, v___x_4933_);
                lean_dec(v_i_4898_);
                v_i_4898_ = v___x_4934_;
                state = 0;
                continue;
            }
            5 => {
                v___x_4942_ = lean_st_ref_take(v_a_4901_);
                v_fvarId_4943_ = lean_ctor_get(v_val_4917_, 0);
                lean_inc(v_fvarId_4943_);
                v_binderName_4944_ = lean_ctor_get(v_val_4917_, 1);
                lean_inc(v_binderName_4944_);
                lean_dec(v_val_4917_);
                v_lctx_4945_ = lean_ctor_get(v___x_4942_, 0);
                v_nextIdx_4946_ = lean_ctor_get(v___x_4942_, 1);
                v_isSharedCheck_4971_ = (!lean_is_exclusive(v___x_4942_)) as u8;
                if v_isSharedCheck_4971_ == 0 {
                    v___x_4948_ = v___x_4942_;
                    v_isShared_4949_ = v_isSharedCheck_4971_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_nextIdx_4946_);
                    lean_inc(v_lctx_4945_);
                    lean_dec(v___x_4942_);
                    v___x_4948_ = lean_box(0);
                    v_isShared_4949_ = v_isSharedCheck_4971_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4950_ = 1;
                v_decl_4951_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v_decl_4951_, 0, v_fvarId_4943_);
                lean_ctor_set(v_decl_4951_, 1, v_binderName_4944_);
                lean_ctor_set(v_decl_4951_, 2, v_snd_4938_);
                lean_ctor_set(v_decl_4951_, 3, v_fst_4920_);
                lean_inc_ref(v_decl_4951_);
                v___x_4952_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_4950_, v_lctx_4945_, v_decl_4951_);
                if v_isShared_4949_ == 0 {
                    lean_ctor_set(v___x_4948_, 0, v___x_4952_);
                    v___x_4954_ = v___x_4948_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4952_);
                    lean_ctor_set(v_reuseFailAlloc_4970_, 1, v_nextIdx_4946_);
                    v___x_4954_ = v_reuseFailAlloc_4970_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4955_ = lean_st_ref_set(v_a_4901_, v___x_4954_);
                v___x_4956_ = lean_unsigned_to_nat(1);
                v___x_4957_ = lean_nat_add(v_i_4898_, v___x_4956_);
                lean_dec(v_i_4898_);
                v___x_4958_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(
                        v_discr_4893_,
                        v_k_4894_,
                        v_ctorInfo_4895_,
                        v_params_4896_,
                        v_fields_4897_,
                        v___x_4957_,
                        v_a_4899_,
                        v_a_4900_,
                        v_a_4901_,
                        v_a_4902_,
                        v_a_4903_,
                    );
                if lean_obj_tag(v___x_4958_) == 0 {
                    v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
                    v_isSharedCheck_4969_ = (!lean_is_exclusive(v___x_4958_)) as u8;
                    if v_isSharedCheck_4969_ == 0 {
                        v___x_4961_ = v___x_4958_;
                        v_isShared_4962_ = v_isSharedCheck_4969_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4959_);
                        lean_dec(v___x_4958_);
                        v___x_4961_ = lean_box(0);
                        v_isShared_4962_ = v_isSharedCheck_4969_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_decl_4951_, 4);
                    lean_del_object(v___x_4940_);
                    return v___x_4958_;
                }
            }
            8 => {
                if v_isShared_4941_ == 0 {
                    lean_ctor_set(v___x_4940_, 1, v_a_4959_);
                    lean_ctor_set(v___x_4940_, 0, v_decl_4951_);
                    v___x_4964_ = v___x_4940_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_decl_4951_);
                    lean_ctor_set(v_reuseFailAlloc_4968_, 1, v_a_4959_);
                    v___x_4964_ = v_reuseFailAlloc_4968_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4962_ == 0 {
                    lean_ctor_set(v___x_4961_, 0, v___x_4964_);
                    v___x_4966_ = v___x_4961_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4964_);
                    v___x_4966_ = v_reuseFailAlloc_4967_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4966_;
            }
            11 => {
                v___x_4976_ = lean_array_get_size(v_fields_4897_);
                v___x_4977_ = lean_nat_dec_lt(v_i_4898_, v___x_4976_);
                if v___x_4977_ == 0 {
                    v___x_4978_ = lean_box(0);
                    v___y_4914_ = v___y_4975_;
                    v___y_4915_ = v___x_4978_;
                    state = 2;
                    continue;
                } else {
                    v___x_4979_ = lean_array_fget_borrowed(v_fields_4897_, v_i_4898_);
                    lean_inc(v___x_4979_);
                    v___x_4980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4980_, 0, v___x_4979_);
                    v___y_4914_ = v___y_4975_;
                    v___y_4915_ = v___x_4980_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(
    mut v_discr_4986_: *mut LeanObject,
    mut v_alt_4987_: *mut LeanObject,
    mut v_a_4988_: *mut LeanObject,
    mut v_a_4989_: *mut LeanObject,
    mut v_a_4990_: *mut LeanObject,
    mut v_a_4991_: *mut LeanObject,
    mut v_a_4992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctorName_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorInfo_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInfo_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5003_: u8 = 0;
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5009_: u8 = 0;
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut v_a_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5024_: u8 = 0;
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut v_a_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5029_: u8 = 0;
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5033_: u8 = 0;
    let mut v_code_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5037_: u8 = 0;
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5042_: u8 = 0;
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5049_: u8 = 0;
    let mut v_a_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5053_: u8 = 0;
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5057_: u8 = 0;
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_alt_4987_) == 0 {
                    v_ctorName_4994_ = lean_ctor_get(v_alt_4987_, 0);
                    lean_inc(v_ctorName_4994_);
                    v_params_4995_ = lean_ctor_get(v_alt_4987_, 1);
                    lean_inc_ref(v_params_4995_);
                    v_code_4996_ = lean_ctor_get(v_alt_4987_, 2);
                    lean_inc_ref(v_code_4996_);
                    lean_dec_ref_known(v_alt_4987_, 3);
                    v___x_4997_ =
                        l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_4994_, v_a_4991_, v_a_4992_);
                    if lean_obj_tag(v___x_4997_) == 0 {
                        v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
                        lean_inc(v_a_4998_);
                        lean_dec_ref_known(v___x_4997_, 1);
                        v_ctorInfo_4999_ = lean_ctor_get(v_a_4998_, 0);
                        v_fieldInfo_5000_ = lean_ctor_get(v_a_4998_, 1);
                        v_isSharedCheck_5025_ = (!lean_is_exclusive(v_a_4998_)) as u8;
                        if v_isSharedCheck_5025_ == 0 {
                            v___x_5002_ = v_a_4998_;
                            v_isShared_5003_ = v_isSharedCheck_5025_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_fieldInfo_5000_);
                            lean_inc(v_ctorInfo_4999_);
                            lean_dec(v_a_4998_);
                            v___x_5002_ = lean_box(0);
                            v_isShared_5003_ = v_isSharedCheck_5025_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_code_4996_);
                        lean_dec_ref(v_params_4995_);
                        lean_dec(v_discr_4986_);
                        v_a_5026_ = lean_ctor_get(v___x_4997_, 0);
                        v_isSharedCheck_5033_ = (!lean_is_exclusive(v___x_4997_)) as u8;
                        if v_isSharedCheck_5033_ == 0 {
                            v___x_5028_ = v___x_4997_;
                            v_isShared_5029_ = v_isSharedCheck_5033_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5026_);
                            lean_dec(v___x_4997_);
                            v___x_5028_ = lean_box(0);
                            v_isShared_5029_ = v_isSharedCheck_5033_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_discr_4986_);
                    v_code_5034_ = lean_ctor_get(v_alt_4987_, 0);
                    v_isSharedCheck_5058_ = (!lean_is_exclusive(v_alt_4987_)) as u8;
                    if v_isSharedCheck_5058_ == 0 {
                        v___x_5036_ = v_alt_4987_;
                        v_isShared_5037_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_code_5034_);
                        lean_dec(v_alt_4987_);
                        v___x_5036_ = lean_box(0);
                        v_isShared_5037_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5004_ = lean_unsigned_to_nat(0);
                v___x_5005_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(
                        v_discr_4986_,
                        v_code_4996_,
                        v_ctorInfo_4999_,
                        v_params_4995_,
                        v_fieldInfo_5000_,
                        v___x_5004_,
                        v_a_4988_,
                        v_a_4989_,
                        v_a_4990_,
                        v_a_4991_,
                        v_a_4992_,
                    );
                lean_dec_ref(v_fieldInfo_5000_);
                lean_dec_ref(v_params_4995_);
                if lean_obj_tag(v___x_5005_) == 0 {
                    v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
                    v_isSharedCheck_5016_ = (!lean_is_exclusive(v___x_5005_)) as u8;
                    if v_isSharedCheck_5016_ == 0 {
                        v___x_5008_ = v___x_5005_;
                        v_isShared_5009_ = v_isSharedCheck_5016_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5006_);
                        lean_dec(v___x_5005_);
                        v___x_5008_ = lean_box(0);
                        v_isShared_5009_ = v_isSharedCheck_5016_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5002_);
                    lean_dec_ref(v_ctorInfo_4999_);
                    v_a_5017_ = lean_ctor_get(v___x_5005_, 0);
                    v_isSharedCheck_5024_ = (!lean_is_exclusive(v___x_5005_)) as u8;
                    if v_isSharedCheck_5024_ == 0 {
                        v___x_5019_ = v___x_5005_;
                        v_isShared_5020_ = v_isSharedCheck_5024_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5017_);
                        lean_dec(v___x_5005_);
                        v___x_5019_ = lean_box(0);
                        v_isShared_5020_ = v_isSharedCheck_5024_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5003_ == 0 {
                    lean_ctor_set_tag(v___x_5002_, 1);
                    lean_ctor_set(v___x_5002_, 1, v_a_5006_);
                    v___x_5011_ = v___x_5002_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_ctorInfo_4999_);
                    lean_ctor_set(v_reuseFailAlloc_5015_, 1, v_a_5006_);
                    v___x_5011_ = v_reuseFailAlloc_5015_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5009_ == 0 {
                    lean_ctor_set(v___x_5008_, 0, v___x_5011_);
                    v___x_5013_ = v___x_5008_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5011_);
                    v___x_5013_ = v_reuseFailAlloc_5014_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5013_;
            }
            5 => {
                if v_isShared_5020_ == 0 {
                    v___x_5022_ = v___x_5019_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
                    v___x_5022_ = v_reuseFailAlloc_5023_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5022_;
            }
            7 => {
                if v_isShared_5029_ == 0 {
                    v___x_5031_ = v___x_5028_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
                    v___x_5031_ = v_reuseFailAlloc_5032_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5031_;
            }
            9 => {
                v___x_5038_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_code_5034_,
                        v_a_4988_,
                        v_a_4989_,
                        v_a_4990_,
                        v_a_4991_,
                        v_a_4992_,
                    );
                if lean_obj_tag(v___x_5038_) == 0 {
                    v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
                    v_isSharedCheck_5049_ = (!lean_is_exclusive(v___x_5038_)) as u8;
                    if v_isSharedCheck_5049_ == 0 {
                        v___x_5041_ = v___x_5038_;
                        v_isShared_5042_ = v_isSharedCheck_5049_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5039_);
                        lean_dec(v___x_5038_);
                        v___x_5041_ = lean_box(0);
                        v_isShared_5042_ = v_isSharedCheck_5049_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5036_);
                    v_a_5050_ = lean_ctor_get(v___x_5038_, 0);
                    v_isSharedCheck_5057_ = (!lean_is_exclusive(v___x_5038_)) as u8;
                    if v_isSharedCheck_5057_ == 0 {
                        v___x_5052_ = v___x_5038_;
                        v_isShared_5053_ = v_isSharedCheck_5057_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_5050_);
                        lean_dec(v___x_5038_);
                        v___x_5052_ = lean_box(0);
                        v_isShared_5053_ = v_isSharedCheck_5057_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_5037_ == 0 {
                    lean_ctor_set(v___x_5036_, 0, v_a_5039_);
                    v___x_5044_ = v___x_5036_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5039_);
                    v___x_5044_ = v_reuseFailAlloc_5048_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5042_ == 0 {
                    lean_ctor_set(v___x_5041_, 0, v___x_5044_);
                    v___x_5046_ = v___x_5041_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
                    v___x_5046_ = v_reuseFailAlloc_5047_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5046_;
            }
            13 => {
                if v_isShared_5053_ == 0 {
                    v___x_5055_ = v___x_5052_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
                    v___x_5055_ = v_reuseFailAlloc_5056_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(
    mut v_fvarId_5059_: *mut LeanObject,
    mut v_sz_5060_: usize,
    mut v_i_5061_: usize,
    mut v_bs_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
    mut v___y_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5069_: u8 = 0;
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: usize = 0;
    let mut v___x_5077_: usize = 0;
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5069_ = lean_usize_dec_lt(v_i_5061_, v_sz_5060_);
                if v___x_5069_ == 0 {
                    lean_dec(v_fvarId_5059_);
                    v___x_5070_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5070_, 0, v_bs_5062_);
                    return v___x_5070_;
                } else {
                    v_v_5071_ = lean_array_uget_borrowed(v_bs_5062_, v_i_5061_);
                    lean_inc(v_v_5071_);
                    lean_inc(v_fvarId_5059_);
                    v___x_5072_ =
                        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(
                            v_fvarId_5059_,
                            v_v_5071_,
                            v___y_5063_,
                            v___y_5064_,
                            v___y_5065_,
                            v___y_5066_,
                            v___y_5067_,
                        );
                    if lean_obj_tag(v___x_5072_) == 0 {
                        v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
                        lean_inc(v_a_5073_);
                        lean_dec_ref_known(v___x_5072_, 1);
                        v___x_5074_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5075_ = lean_array_uset(v_bs_5062_, v_i_5061_, v___x_5074_);
                        v___x_5076_ = 1usize;
                        v___x_5077_ = lean_usize_add(v_i_5061_, v___x_5076_);
                        v___x_5078_ = lean_array_uset(v_bs_x27_5075_, v_i_5061_, v_a_5073_);
                        v_i_5061_ = v___x_5077_;
                        v_bs_5062_ = v___x_5078_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5062_);
                        lean_dec(v_fvarId_5059_);
                        v_a_5080_ = lean_ctor_get(v___x_5072_, 0);
                        v_isSharedCheck_5087_ = (!lean_is_exclusive(v___x_5072_)) as u8;
                        if v_isSharedCheck_5087_ == 0 {
                            v___x_5082_ = v___x_5072_;
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5080_);
                            lean_dec(v___x_5072_);
                            v___x_5082_ = lean_box(0);
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5083_ == 0 {
                    v___x_5085_ = v___x_5082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5086_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
    mut v_c_5088_: *mut LeanObject,
    mut v_a_5089_: *mut LeanObject,
    mut v_a_5090_: *mut LeanObject,
    mut v_a_5091_: *mut LeanObject,
    mut v_a_5092_: *mut LeanObject,
    mut v_a_5093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5104_: u8 = 0;
    let mut v_fvarId_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5112_: u8 = 0;
    let mut v_sz_5113_: usize = 0;
    let mut v___x_5114_: usize = 0;
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5122_: u8 = 0;
    let mut v_sz_5123_: usize = 0;
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5140_: u8 = 0;
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5162_: u8 = 0;
    let mut v_isSharedCheck_5163_: u8 = 0;
    let mut v_a_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: u8 = 0;
    let mut v___x_5177_: u8 = 0;
    let mut v___x_5178_: usize = 0;
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: usize = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut v_a_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut v_fvarId_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5198_: u8 = 0;
    let mut v_a_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jpParamMask_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: u8 = 0;
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: usize = 0;
    let mut v___x_5226_: usize = 0;
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: usize = 0;
    let mut v___x_5229_: usize = 0;
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5231_: u8 = 0;
    let mut v_cases_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5235_: u8 = 0;
    let mut v_typeName_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5242_: u8 = 0;
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldIdx_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5272_: u8 = 0;
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5276_: u8 = 0;
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: u8 = 0;
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5286_: usize = 0;
    let mut v___x_5287_: usize = 0;
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5306_: u8 = 0;
    let mut v_a_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5310_: u8 = 0;
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5314_: u8 = 0;
    let mut v_a_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5322_: u8 = 0;
    let mut v_a_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5326_: u8 = 0;
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5330_: u8 = 0;
    let mut v___x_5331_: u8 = 0;
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5336_: u8 = 0;
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5340_: u8 = 0;
    let mut v_isSharedCheck_5341_: u8 = 0;
    let mut v_isSharedCheck_5342_: u8 = 0;
    let mut v_fvarId_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: u8 = 0;
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5361_: u8 = 0;
    let mut v___x_5362_: u8 = 0;
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5364_: u8 = 0;
    let mut v_type_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5368_: u8 = 0;
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5373_: u8 = 0;
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5380_: u8 = 0;
    let mut v_a_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5384_: u8 = 0;
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5388_: u8 = 0;
    let mut v_isSharedCheck_5389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_c_5088_) {
                0 => {
                    v_decl_5095_ = lean_ctor_get(v_c_5088_, 0);
                    lean_inc_ref(v_decl_5095_);
                    v_k_5096_ = lean_ctor_get(v_c_5088_, 1);
                    lean_inc_ref(v_k_5096_);
                    lean_dec_ref_known(v_c_5088_, 2);
                    v___x_5097_ =
                        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(
                            v_decl_5095_,
                            v_k_5096_,
                            v_a_5089_,
                            v_a_5090_,
                            v_a_5091_,
                            v_a_5092_,
                            v_a_5093_,
                        );
                    return v___x_5097_;
                }
                1 => {
                    lean_dec_ref_known(v_c_5088_, 2);
                    v___x_5098_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
                    v___x_5099_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_5098_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
                    return v___x_5099_;
                }
                2 => {
                    v_decl_5100_ = lean_ctor_get(v_c_5088_, 0);
                    v_k_5101_ = lean_ctor_get(v_c_5088_, 1);
                    v_isSharedCheck_5193_ = (!lean_is_exclusive(v_c_5088_)) as u8;
                    if v_isSharedCheck_5193_ == 0 {
                        v___x_5103_ = v_c_5088_;
                        v_isShared_5104_ = v_isSharedCheck_5193_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_5101_);
                        lean_inc(v_decl_5100_);
                        lean_dec(v_c_5088_);
                        v___x_5103_ = lean_box(0);
                        v_isShared_5104_ = v_isSharedCheck_5193_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_fvarId_5194_ = lean_ctor_get(v_c_5088_, 0);
                    v_args_5195_ = lean_ctor_get(v_c_5088_, 1);
                    v_isSharedCheck_5231_ = (!lean_is_exclusive(v_c_5088_)) as u8;
                    if v_isSharedCheck_5231_ == 0 {
                        v___x_5197_ = v_c_5088_;
                        v_isShared_5198_ = v_isSharedCheck_5231_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_args_5195_);
                        lean_inc(v_fvarId_5194_);
                        lean_dec(v_c_5088_);
                        v___x_5197_ = lean_box(0);
                        v_isShared_5198_ = v_isSharedCheck_5231_;
                        state = 16;
                        continue;
                    }
                }
                4 => {
                    v_cases_5232_ = lean_ctor_get(v_c_5088_, 0);
                    v_isSharedCheck_5342_ = (!lean_is_exclusive(v_c_5088_)) as u8;
                    if v_isSharedCheck_5342_ == 0 {
                        v___x_5234_ = v_c_5088_;
                        v_isShared_5235_ = v_isSharedCheck_5342_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_cases_5232_);
                        lean_dec(v_c_5088_);
                        v___x_5234_ = lean_box(0);
                        v_isShared_5235_ = v_isSharedCheck_5342_;
                        state = 22;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_5343_ = lean_ctor_get(v_c_5088_, 0);
                    v_isSharedCheck_5364_ = (!lean_is_exclusive(v_c_5088_)) as u8;
                    if v_isSharedCheck_5364_ == 0 {
                        v___x_5345_ = v_c_5088_;
                        v_isShared_5346_ = v_isSharedCheck_5364_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_fvarId_5343_);
                        lean_dec(v_c_5088_);
                        v___x_5345_ = lean_box(0);
                        v_isShared_5346_ = v_isSharedCheck_5364_;
                        state = 38;
                        continue;
                    }
                }
                _ => {
                    v_type_5365_ = lean_ctor_get(v_c_5088_, 0);
                    v_isSharedCheck_5389_ = (!lean_is_exclusive(v_c_5088_)) as u8;
                    if v_isSharedCheck_5389_ == 0 {
                        v___x_5367_ = v_c_5088_;
                        v_isShared_5368_ = v_isSharedCheck_5389_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_type_5365_);
                        lean_dec(v_c_5088_);
                        v___x_5367_ = lean_box(0);
                        v_isShared_5368_ = v_isSharedCheck_5389_;
                        state = 42;
                        continue;
                    }
                }
            },
            1 => {
                v_fvarId_5105_ = lean_ctor_get(v_decl_5100_, 0);
                v_binderName_5106_ = lean_ctor_get(v_decl_5100_, 1);
                v_params_5107_ = lean_ctor_get(v_decl_5100_, 2);
                v_type_5108_ = lean_ctor_get(v_decl_5100_, 3);
                v_value_5109_ = lean_ctor_get(v_decl_5100_, 4);
                v_isSharedCheck_5192_ = (!lean_is_exclusive(v_decl_5100_)) as u8;
                if v_isSharedCheck_5192_ == 0 {
                    v___x_5111_ = v_decl_5100_;
                    v_isShared_5112_ = v_isSharedCheck_5192_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_value_5109_);
                    lean_inc(v_type_5108_);
                    lean_inc(v_params_5107_);
                    lean_inc(v_binderName_5106_);
                    lean_inc(v_fvarId_5105_);
                    lean_dec(v_decl_5100_);
                    v___x_5111_ = lean_box(0);
                    v_isShared_5112_ = v_isSharedCheck_5192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_5113_ = lean_array_size(v_params_5107_);
                v___x_5114_ = 0usize;
                v___x_5115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_5113_, v___x_5114_, v_params_5107_, v_a_5089_, v_a_5091_, v_a_5092_, v_a_5093_);
                if lean_obj_tag(v___x_5115_) == 0 {
                    v_a_5116_ = lean_ctor_get(v___x_5115_, 0);
                    lean_inc(v_a_5116_);
                    lean_dec_ref_known(v___x_5115_, 1);
                    v___x_5117_ = lean_st_ref_take(v_a_5089_);
                    v_subst_5118_ = lean_ctor_get(v___x_5117_, 0);
                    v_jpParamMask_5119_ = lean_ctor_get(v___x_5117_, 1);
                    v_isSharedCheck_5183_ = (!lean_is_exclusive(v___x_5117_)) as u8;
                    if v_isSharedCheck_5183_ == 0 {
                        v___x_5121_ = v___x_5117_;
                        v_isShared_5122_ = v_isSharedCheck_5183_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_jpParamMask_5119_);
                        lean_inc(v_subst_5118_);
                        lean_dec(v___x_5117_);
                        v___x_5121_ = lean_box(0);
                        v_isShared_5122_ = v_isSharedCheck_5183_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5111_);
                    lean_dec_ref(v_value_5109_);
                    lean_dec_ref(v_type_5108_);
                    lean_dec(v_binderName_5106_);
                    lean_dec(v_fvarId_5105_);
                    lean_del_object(v___x_5103_);
                    lean_dec_ref(v_k_5101_);
                    v_a_5184_ = lean_ctor_get(v___x_5115_, 0);
                    v_isSharedCheck_5191_ = (!lean_is_exclusive(v___x_5115_)) as u8;
                    if v_isSharedCheck_5191_ == 0 {
                        v___x_5186_ = v___x_5115_;
                        v_isShared_5187_ = v_isSharedCheck_5191_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_5184_);
                        lean_dec(v___x_5115_);
                        v___x_5186_ = lean_box(0);
                        v_isShared_5187_ = v_isSharedCheck_5191_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                v_sz_5123_ = lean_array_size(v_a_5116_);
                lean_inc(v_a_5116_);
                v___x_5124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_5123_, v___x_5114_, v_a_5116_);
                lean_inc_ref(v___x_5124_);
                lean_inc(v_fvarId_5105_);
                v___x_5125_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_5119_, v_fvarId_5105_, v___x_5124_);
                if v_isShared_5122_ == 0 {
                    lean_ctor_set(v___x_5121_, 1, v___x_5125_);
                    v___x_5127_ = v___x_5121_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5182_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_subst_5118_);
                    lean_ctor_set(v_reuseFailAlloc_5182_, 1, v___x_5125_);
                    v___x_5127_ = v_reuseFailAlloc_5182_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5128_ = lean_st_ref_set(v_a_5089_, v___x_5127_);
                v___x_5172_ = lean_unsigned_to_nat(0);
                v___x_5173_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3;
                v___x_5174_ = l_Array_zip___redArg(v_a_5116_, v___x_5124_);
                lean_dec_ref(v___x_5124_);
                v___x_5175_ = lean_array_get_size(v___x_5174_);
                v___x_5176_ = lean_nat_dec_lt(v___x_5172_, v___x_5175_);
                if v___x_5176_ == 0 {
                    lean_dec_ref(v___x_5174_);
                    v___y_5130_ = v___x_5173_;
                    state = 5;
                    continue;
                } else {
                    v___x_5177_ = lean_nat_dec_le(v___x_5175_, v___x_5175_);
                    if v___x_5177_ == 0 {
                        if v___x_5176_ == 0 {
                            lean_dec_ref(v___x_5174_);
                            v___y_5130_ = v___x_5173_;
                            state = 5;
                            continue;
                        } else {
                            v___x_5178_ = lean_usize_of_nat(v___x_5175_);
                            v___x_5179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_5174_, v___x_5114_, v___x_5178_, v___x_5173_);
                            lean_dec_ref(v___x_5174_);
                            v___y_5130_ = v___x_5179_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_5180_ = lean_usize_of_nat(v___x_5175_);
                        v___x_5181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_5174_, v___x_5114_, v___x_5180_, v___x_5173_);
                        lean_dec_ref(v___x_5174_);
                        v___y_5130_ = v___x_5181_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5131_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_value_5109_,
                        v_a_5089_,
                        v_a_5090_,
                        v_a_5091_,
                        v_a_5092_,
                        v_a_5093_,
                    );
                if lean_obj_tag(v___x_5131_) == 0 {
                    v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
                    lean_inc(v_a_5132_);
                    lean_dec_ref_known(v___x_5131_, 1);
                    v___x_5133_ =
                        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                            v_k_5101_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_,
                        );
                    if lean_obj_tag(v___x_5133_) == 0 {
                        v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
                        lean_inc(v_a_5134_);
                        lean_dec_ref_known(v___x_5133_, 1);
                        v___x_5135_ = lean_array_get_size(v_a_5116_);
                        lean_dec(v_a_5116_);
                        v___x_5136_ = l_Lean_Compiler_LCNF_lowerResultType(
                            v_type_5108_,
                            v___x_5135_,
                            v_a_5092_,
                            v_a_5093_,
                        );
                        lean_dec_ref(v_type_5108_);
                        if lean_obj_tag(v___x_5136_) == 0 {
                            v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
                            v_isSharedCheck_5163_ = (!lean_is_exclusive(v___x_5136_)) as u8;
                            if v_isSharedCheck_5163_ == 0 {
                                v___x_5139_ = v___x_5136_;
                                v_isShared_5140_ = v_isSharedCheck_5163_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_5137_);
                                lean_dec(v___x_5136_);
                                v___x_5139_ = lean_box(0);
                                v_isShared_5140_ = v_isSharedCheck_5163_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5134_);
                            lean_dec(v_a_5132_);
                            lean_dec_ref(v___y_5130_);
                            lean_del_object(v___x_5111_);
                            lean_dec(v_binderName_5106_);
                            lean_dec(v_fvarId_5105_);
                            lean_del_object(v___x_5103_);
                            v_a_5164_ = lean_ctor_get(v___x_5136_, 0);
                            v_isSharedCheck_5171_ = (!lean_is_exclusive(v___x_5136_)) as u8;
                            if v_isSharedCheck_5171_ == 0 {
                                v___x_5166_ = v___x_5136_;
                                v_isShared_5167_ = v_isSharedCheck_5171_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_5164_);
                                lean_dec(v___x_5136_);
                                v___x_5166_ = lean_box(0);
                                v_isShared_5167_ = v_isSharedCheck_5171_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5132_);
                        lean_dec_ref(v___y_5130_);
                        lean_dec(v_a_5116_);
                        lean_del_object(v___x_5111_);
                        lean_dec_ref(v_type_5108_);
                        lean_dec(v_binderName_5106_);
                        lean_dec(v_fvarId_5105_);
                        lean_del_object(v___x_5103_);
                        return v___x_5133_;
                    }
                } else {
                    lean_dec_ref(v___y_5130_);
                    lean_dec(v_a_5116_);
                    lean_del_object(v___x_5111_);
                    lean_dec_ref(v_type_5108_);
                    lean_dec(v_binderName_5106_);
                    lean_dec(v_fvarId_5105_);
                    lean_del_object(v___x_5103_);
                    lean_dec_ref(v_k_5101_);
                    return v___x_5131_;
                }
            }
            6 => {
                v___x_5141_ = lean_st_ref_take(v_a_5091_);
                v_lctx_5142_ = lean_ctor_get(v___x_5141_, 0);
                v_nextIdx_5143_ = lean_ctor_get(v___x_5141_, 1);
                v_isSharedCheck_5162_ = (!lean_is_exclusive(v___x_5141_)) as u8;
                if v_isSharedCheck_5162_ == 0 {
                    v___x_5145_ = v___x_5141_;
                    v_isShared_5146_ = v_isSharedCheck_5162_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_nextIdx_5143_);
                    lean_inc(v_lctx_5142_);
                    lean_dec(v___x_5141_);
                    v___x_5145_ = lean_box(0);
                    v_isShared_5146_ = v_isSharedCheck_5162_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5147_ = 1;
                if v_isShared_5112_ == 0 {
                    lean_ctor_set(v___x_5111_, 4, v_a_5132_);
                    lean_ctor_set(v___x_5111_, 3, v_a_5137_);
                    lean_ctor_set(v___x_5111_, 2, v___y_5130_);
                    v___x_5149_ = v___x_5111_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_fvarId_5105_);
                    lean_ctor_set(v_reuseFailAlloc_5161_, 1, v_binderName_5106_);
                    lean_ctor_set(v_reuseFailAlloc_5161_, 2, v___y_5130_);
                    lean_ctor_set(v_reuseFailAlloc_5161_, 3, v_a_5137_);
                    lean_ctor_set(v_reuseFailAlloc_5161_, 4, v_a_5132_);
                    v___x_5149_ = v_reuseFailAlloc_5161_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v___x_5149_);
                v___x_5150_ =
                    l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_5147_, v_lctx_5142_, v___x_5149_);
                if v_isShared_5146_ == 0 {
                    lean_ctor_set(v___x_5145_, 0, v___x_5150_);
                    v___x_5152_ = v___x_5145_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5150_);
                    lean_ctor_set(v_reuseFailAlloc_5160_, 1, v_nextIdx_5143_);
                    v___x_5152_ = v_reuseFailAlloc_5160_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5153_ = lean_st_ref_set(v_a_5091_, v___x_5152_);
                if v_isShared_5104_ == 0 {
                    lean_ctor_set(v___x_5103_, 1, v_a_5134_);
                    lean_ctor_set(v___x_5103_, 0, v___x_5149_);
                    v___x_5155_ = v___x_5103_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5159_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5149_);
                    lean_ctor_set(v_reuseFailAlloc_5159_, 1, v_a_5134_);
                    v___x_5155_ = v_reuseFailAlloc_5159_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5140_ == 0 {
                    lean_ctor_set(v___x_5139_, 0, v___x_5155_);
                    v___x_5157_ = v___x_5139_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5155_);
                    v___x_5157_ = v_reuseFailAlloc_5158_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5157_;
            }
            12 => {
                if v_isShared_5167_ == 0 {
                    v___x_5169_ = v___x_5166_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
                    v___x_5169_ = v_reuseFailAlloc_5170_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5169_;
            }
            14 => {
                if v_isShared_5187_ == 0 {
                    v___x_5189_ = v___x_5186_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
                    v___x_5189_ = v_reuseFailAlloc_5190_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5189_;
            }
            16 => {
                v___x_5216_ = lean_st_ref_get(v_a_5089_);
                v_jpParamMask_5217_ = lean_ctor_get(v___x_5216_, 1);
                lean_inc_ref(v_jpParamMask_5217_);
                lean_dec(v___x_5216_);
                v___x_5218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_5217_, v_fvarId_5194_);
                lean_dec_ref(v_jpParamMask_5217_);
                v___x_5219_ = lean_unsigned_to_nat(0);
                v___x_5220_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4;
                v___x_5221_ = l_Array_zip___redArg(v_args_5195_, v___x_5218_);
                lean_dec_ref(v___x_5218_);
                lean_dec_ref(v_args_5195_);
                v___x_5222_ = lean_array_get_size(v___x_5221_);
                v___x_5223_ = lean_nat_dec_lt(v___x_5219_, v___x_5222_);
                if v___x_5223_ == 0 {
                    lean_dec_ref(v___x_5221_);
                    v_a_5200_ = v___x_5220_;
                    state = 17;
                    continue;
                } else {
                    v___x_5224_ = lean_nat_dec_le(v___x_5222_, v___x_5222_);
                    if v___x_5224_ == 0 {
                        if v___x_5223_ == 0 {
                            lean_dec_ref(v___x_5221_);
                            v_a_5200_ = v___x_5220_;
                            state = 17;
                            continue;
                        } else {
                            v___x_5225_ = 0usize;
                            v___x_5226_ = lean_usize_of_nat(v___x_5222_);
                            v___x_5227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_5221_, v___x_5225_, v___x_5226_, v___x_5220_, v_a_5089_);
                            lean_dec_ref(v___x_5221_);
                            v___y_5206_ = v___x_5227_;
                            state = 19;
                            continue;
                        }
                    } else {
                        v___x_5228_ = 0usize;
                        v___x_5229_ = lean_usize_of_nat(v___x_5222_);
                        v___x_5230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_5221_, v___x_5228_, v___x_5229_, v___x_5220_, v_a_5089_);
                        lean_dec_ref(v___x_5221_);
                        v___y_5206_ = v___x_5230_;
                        state = 19;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_5198_ == 0 {
                    lean_ctor_set(v___x_5197_, 1, v_a_5200_);
                    v___x_5202_ = v___x_5197_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_fvarId_5194_);
                    lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_a_5200_);
                    v___x_5202_ = v_reuseFailAlloc_5204_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_5203_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5203_, 0, v___x_5202_);
                return v___x_5203_;
            }
            19 => {
                if lean_obj_tag(v___y_5206_) == 0 {
                    v_a_5207_ = lean_ctor_get(v___y_5206_, 0);
                    lean_inc(v_a_5207_);
                    lean_dec_ref_known(v___y_5206_, 1);
                    v_a_5200_ = v_a_5207_;
                    state = 17;
                    continue;
                } else {
                    lean_del_object(v___x_5197_);
                    lean_dec(v_fvarId_5194_);
                    v_a_5208_ = lean_ctor_get(v___y_5206_, 0);
                    v_isSharedCheck_5215_ = (!lean_is_exclusive(v___y_5206_)) as u8;
                    if v_isSharedCheck_5215_ == 0 {
                        v___x_5210_ = v___y_5206_;
                        v_isShared_5211_ = v_isSharedCheck_5215_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_5208_);
                        lean_dec(v___y_5206_);
                        v___x_5210_ = lean_box(0);
                        v_isShared_5211_ = v_isSharedCheck_5215_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_5211_ == 0 {
                    v___x_5213_ = v___x_5210_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
                    v___x_5213_ = v_reuseFailAlloc_5214_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5213_;
            }
            22 => {
                v_typeName_5236_ = lean_ctor_get(v_cases_5232_, 0);
                v_resultType_5237_ = lean_ctor_get(v_cases_5232_, 1);
                v_discr_5238_ = lean_ctor_get(v_cases_5232_, 2);
                v_alts_5239_ = lean_ctor_get(v_cases_5232_, 3);
                v_isSharedCheck_5341_ = (!lean_is_exclusive(v_cases_5232_)) as u8;
                if v_isSharedCheck_5341_ == 0 {
                    v___x_5241_ = v_cases_5232_;
                    v_isShared_5242_ = v_isSharedCheck_5341_;
                    state = 23;
                    continue;
                } else {
                    lean_inc(v_alts_5239_);
                    lean_inc(v_discr_5238_);
                    lean_inc(v_resultType_5237_);
                    lean_inc(v_typeName_5236_);
                    lean_dec(v_cases_5232_);
                    v___x_5241_ = lean_box(0);
                    v_isShared_5242_ = v_isSharedCheck_5341_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                lean_inc(v_typeName_5236_);
                v___x_5243_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(
                    v_typeName_5236_,
                    v_a_5092_,
                    v_a_5093_,
                );
                if lean_obj_tag(v___x_5243_) == 0 {
                    v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
                    lean_inc(v_a_5244_);
                    lean_dec_ref_known(v___x_5243_, 1);
                    if lean_obj_tag(v_a_5244_) == 1 {
                        lean_del_object(v___x_5241_);
                        lean_dec_ref(v_resultType_5237_);
                        lean_dec(v_typeName_5236_);
                        lean_del_object(v___x_5234_);
                        v_val_5245_ = lean_ctor_get(v_a_5244_, 0);
                        lean_inc(v_val_5245_);
                        lean_dec_ref_known(v_a_5244_, 1);
                        v___x_5246_ = lean_array_get_size(v_alts_5239_);
                        v___x_5247_ = lean_unsigned_to_nat(1);
                        v___x_5248_ = lean_nat_dec_eq(v___x_5246_, v___x_5247_);
                        if v___x_5248_ == 0 {
                            lean_dec(v_val_5245_);
                            lean_dec_ref(v_alts_5239_);
                            lean_dec(v_discr_5238_);
                            v___x_5249_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6);
                            v___x_5250_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_5249_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
                            return v___x_5250_;
                        } else {
                            v___x_5251_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
                            v___x_5252_ = lean_unsigned_to_nat(0);
                            v___x_5253_ = lean_array_get(v___x_5251_, v_alts_5239_, v___x_5252_);
                            lean_dec_ref(v_alts_5239_);
                            if lean_obj_tag(v___x_5253_) == 0 {
                                v_ctorName_5254_ = lean_ctor_get(v___x_5253_, 0);
                                lean_inc(v_ctorName_5254_);
                                v_params_5255_ = lean_ctor_get(v___x_5253_, 1);
                                lean_inc_ref(v_params_5255_);
                                v_code_5256_ = lean_ctor_get(v___x_5253_, 2);
                                lean_inc_ref(v_code_5256_);
                                lean_dec_ref_known(v___x_5253_, 3);
                                v_ctorName_5257_ = lean_ctor_get(v_val_5245_, 0);
                                lean_inc(v_ctorName_5257_);
                                v_fieldIdx_5258_ = lean_ctor_get(v_val_5245_, 2);
                                lean_inc(v_fieldIdx_5258_);
                                lean_dec(v_val_5245_);
                                v___x_5259_ = lean_name_eq(v_ctorName_5254_, v_ctorName_5257_);
                                lean_dec(v_ctorName_5257_);
                                lean_dec(v_ctorName_5254_);
                                if v___x_5259_ == 0 {
                                    lean_dec(v_fieldIdx_5258_);
                                    lean_dec_ref(v_code_5256_);
                                    lean_dec_ref(v_params_5255_);
                                    lean_dec(v_discr_5238_);
                                    v___x_5260_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
                                    v___x_5261_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_5260_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
                                    return v___x_5261_;
                                } else {
                                    v___x_5262_ = lean_array_get_size(v_params_5255_);
                                    v___x_5263_ = lean_nat_dec_lt(v_fieldIdx_5258_, v___x_5262_);
                                    if v___x_5263_ == 0 {
                                        lean_dec(v_fieldIdx_5258_);
                                        lean_dec_ref(v_code_5256_);
                                        lean_dec_ref(v_params_5255_);
                                        lean_dec(v_discr_5238_);
                                        v___x_5264_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
                                        v___x_5265_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_5264_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
                                        return v___x_5265_;
                                    } else {
                                        v___x_5266_ = lean_box(0);
                                        v___x_5267_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_5262_, v_params_5255_, v_fieldIdx_5258_, v_discr_5238_, v___x_5252_, v___x_5266_, v_a_5089_);
                                        lean_dec(v_fieldIdx_5258_);
                                        lean_dec_ref(v_params_5255_);
                                        if lean_obj_tag(v___x_5267_) == 0 {
                                            lean_dec_ref_known(v___x_5267_, 1);
                                            v_c_5088_ = v_code_5256_;
                                            state = 0;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_code_5256_);
                                            v_a_5269_ = lean_ctor_get(v___x_5267_, 0);
                                            v_isSharedCheck_5276_ =
                                                (!lean_is_exclusive(v___x_5267_)) as u8;
                                            if v_isSharedCheck_5276_ == 0 {
                                                v___x_5271_ = v___x_5267_;
                                                v_isShared_5272_ = v_isSharedCheck_5276_;
                                                state = 24;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5269_);
                                                lean_dec(v___x_5267_);
                                                v___x_5271_ = lean_box(0);
                                                v_isShared_5272_ = v_isSharedCheck_5276_;
                                                state = 24;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v___x_5253_);
                                lean_dec(v_val_5245_);
                                lean_dec(v_discr_5238_);
                                v___x_5277_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
                                v___x_5278_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_5277_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
                                return v___x_5278_;
                            }
                        }
                    } else {
                        lean_dec(v_a_5244_);
                        v___x_5279_ = lean_st_ref_get(v_a_5089_);
                        v_subst_5280_ = lean_ctor_get(v___x_5279_, 0);
                        lean_inc_ref(v_subst_5280_);
                        lean_dec(v___x_5279_);
                        v___x_5281_ = 1;
                        v___x_5282_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_subst_5280_,
                            v_discr_5238_,
                            v___x_5281_,
                        );
                        lean_dec_ref(v_subst_5280_);
                        if lean_obj_tag(v___x_5282_) == 0 {
                            v_fvarId_5283_ = lean_ctor_get(v___x_5282_, 0);
                            lean_inc(v_fvarId_5283_);
                            lean_dec_ref_known(v___x_5282_, 1);
                            v___x_5284_ = l_Lean_Compiler_LCNF_toImpureType(
                                v_resultType_5237_,
                                v_a_5092_,
                                v_a_5093_,
                            );
                            if lean_obj_tag(v___x_5284_) == 0 {
                                v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
                                lean_inc(v_a_5285_);
                                lean_dec_ref_known(v___x_5284_, 1);
                                v_sz_5286_ = lean_array_size(v_alts_5239_);
                                v___x_5287_ = 0usize;
                                lean_inc(v_fvarId_5283_);
                                v___x_5288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_5283_, v_sz_5286_, v___x_5287_, v_alts_5239_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
                                if lean_obj_tag(v___x_5288_) == 0 {
                                    v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
                                    lean_inc(v_a_5289_);
                                    lean_dec_ref_known(v___x_5288_, 1);
                                    v___x_5290_ = l_Lean_Compiler_LCNF_nameToImpureType(
                                        v_typeName_5236_,
                                        v_a_5092_,
                                        v_a_5093_,
                                    );
                                    if lean_obj_tag(v___x_5290_) == 0 {
                                        v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
                                        v_isSharedCheck_5306_ =
                                            (!lean_is_exclusive(v___x_5290_)) as u8;
                                        if v_isSharedCheck_5306_ == 0 {
                                            v___x_5293_ = v___x_5290_;
                                            v_isShared_5294_ = v_isSharedCheck_5306_;
                                            state = 26;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5291_);
                                            lean_dec(v___x_5290_);
                                            v___x_5293_ = lean_box(0);
                                            v_isShared_5294_ = v_isSharedCheck_5306_;
                                            state = 26;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_5289_);
                                        lean_dec(v_a_5285_);
                                        lean_dec(v_fvarId_5283_);
                                        lean_del_object(v___x_5241_);
                                        lean_del_object(v___x_5234_);
                                        v_a_5307_ = lean_ctor_get(v___x_5290_, 0);
                                        v_isSharedCheck_5314_ =
                                            (!lean_is_exclusive(v___x_5290_)) as u8;
                                        if v_isSharedCheck_5314_ == 0 {
                                            v___x_5309_ = v___x_5290_;
                                            v_isShared_5310_ = v_isSharedCheck_5314_;
                                            state = 30;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5307_);
                                            lean_dec(v___x_5290_);
                                            v___x_5309_ = lean_box(0);
                                            v_isShared_5310_ = v_isSharedCheck_5314_;
                                            state = 30;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5285_);
                                    lean_dec(v_fvarId_5283_);
                                    lean_del_object(v___x_5241_);
                                    lean_dec(v_typeName_5236_);
                                    lean_del_object(v___x_5234_);
                                    v_a_5315_ = lean_ctor_get(v___x_5288_, 0);
                                    v_isSharedCheck_5322_ = (!lean_is_exclusive(v___x_5288_)) as u8;
                                    if v_isSharedCheck_5322_ == 0 {
                                        v___x_5317_ = v___x_5288_;
                                        v_isShared_5318_ = v_isSharedCheck_5322_;
                                        state = 32;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5315_);
                                        lean_dec(v___x_5288_);
                                        v___x_5317_ = lean_box(0);
                                        v_isShared_5318_ = v_isSharedCheck_5322_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_fvarId_5283_);
                                lean_del_object(v___x_5241_);
                                lean_dec_ref(v_alts_5239_);
                                lean_dec(v_typeName_5236_);
                                lean_del_object(v___x_5234_);
                                v_a_5323_ = lean_ctor_get(v___x_5284_, 0);
                                v_isSharedCheck_5330_ = (!lean_is_exclusive(v___x_5284_)) as u8;
                                if v_isSharedCheck_5330_ == 0 {
                                    v___x_5325_ = v___x_5284_;
                                    v_isShared_5326_ = v_isSharedCheck_5330_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_a_5323_);
                                    lean_dec(v___x_5284_);
                                    v___x_5325_ = lean_box(0);
                                    v_isShared_5326_ = v_isSharedCheck_5330_;
                                    state = 34;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_5241_);
                            lean_dec_ref(v_alts_5239_);
                            lean_dec_ref(v_resultType_5237_);
                            lean_dec(v_typeName_5236_);
                            lean_del_object(v___x_5234_);
                            v___x_5331_ = 1;
                            v___x_5332_ = l_Lean_Compiler_LCNF_mkReturnErased(
                                v___x_5331_,
                                v_a_5090_,
                                v_a_5091_,
                                v_a_5092_,
                                v_a_5093_,
                            );
                            return v___x_5332_;
                        }
                    }
                } else {
                    lean_del_object(v___x_5241_);
                    lean_dec_ref(v_alts_5239_);
                    lean_dec(v_discr_5238_);
                    lean_dec_ref(v_resultType_5237_);
                    lean_dec(v_typeName_5236_);
                    lean_del_object(v___x_5234_);
                    v_a_5333_ = lean_ctor_get(v___x_5243_, 0);
                    v_isSharedCheck_5340_ = (!lean_is_exclusive(v___x_5243_)) as u8;
                    if v_isSharedCheck_5340_ == 0 {
                        v___x_5335_ = v___x_5243_;
                        v_isShared_5336_ = v_isSharedCheck_5340_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_5333_);
                        lean_dec(v___x_5243_);
                        v___x_5335_ = lean_box(0);
                        v_isShared_5336_ = v_isSharedCheck_5340_;
                        state = 36;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_5272_ == 0 {
                    v___x_5274_ = v___x_5271_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
                    v___x_5274_ = v_reuseFailAlloc_5275_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_5274_;
            }
            26 => {
                v___x_5295_ = l_Lean_Expr_getAppFn(v_a_5291_);
                lean_dec(v_a_5291_);
                v___x_5296_ = l_Lean_Expr_constName_x21(v___x_5295_);
                lean_dec_ref(v___x_5295_);
                if v_isShared_5242_ == 0 {
                    lean_ctor_set(v___x_5241_, 3, v_a_5289_);
                    lean_ctor_set(v___x_5241_, 2, v_fvarId_5283_);
                    lean_ctor_set(v___x_5241_, 1, v_a_5285_);
                    lean_ctor_set(v___x_5241_, 0, v___x_5296_);
                    v___x_5298_ = v___x_5241_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5305_, 0, v___x_5296_);
                    lean_ctor_set(v_reuseFailAlloc_5305_, 1, v_a_5285_);
                    lean_ctor_set(v_reuseFailAlloc_5305_, 2, v_fvarId_5283_);
                    lean_ctor_set(v_reuseFailAlloc_5305_, 3, v_a_5289_);
                    v___x_5298_ = v_reuseFailAlloc_5305_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_5235_ == 0 {
                    lean_ctor_set(v___x_5234_, 0, v___x_5298_);
                    v___x_5300_ = v___x_5234_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5298_);
                    v___x_5300_ = v_reuseFailAlloc_5304_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_5294_ == 0 {
                    lean_ctor_set(v___x_5293_, 0, v___x_5300_);
                    v___x_5302_ = v___x_5293_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5300_);
                    v___x_5302_ = v_reuseFailAlloc_5303_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5302_;
            }
            30 => {
                if v_isShared_5310_ == 0 {
                    v___x_5312_ = v___x_5309_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5313_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5313_, 0, v_a_5307_);
                    v___x_5312_ = v_reuseFailAlloc_5313_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5312_;
            }
            32 => {
                if v_isShared_5318_ == 0 {
                    v___x_5320_ = v___x_5317_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
                    v___x_5320_ = v_reuseFailAlloc_5321_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5320_;
            }
            34 => {
                if v_isShared_5326_ == 0 {
                    v___x_5328_ = v___x_5325_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5323_);
                    v___x_5328_ = v_reuseFailAlloc_5329_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5328_;
            }
            36 => {
                if v_isShared_5336_ == 0 {
                    v___x_5338_ = v___x_5335_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5333_);
                    v___x_5338_ = v_reuseFailAlloc_5339_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_5338_;
            }
            38 => {
                v___x_5347_ = lean_st_ref_get(v_a_5089_);
                v_subst_5348_ = lean_ctor_get(v___x_5347_, 0);
                lean_inc_ref(v_subst_5348_);
                lean_dec(v___x_5347_);
                v___x_5349_ = 1;
                v___x_5350_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v_subst_5348_,
                    v_fvarId_5343_,
                    v___x_5349_,
                );
                lean_dec_ref(v_subst_5348_);
                if lean_obj_tag(v___x_5350_) == 0 {
                    v_fvarId_5351_ = lean_ctor_get(v___x_5350_, 0);
                    v_isSharedCheck_5361_ = (!lean_is_exclusive(v___x_5350_)) as u8;
                    if v_isSharedCheck_5361_ == 0 {
                        v___x_5353_ = v___x_5350_;
                        v_isShared_5354_ = v_isSharedCheck_5361_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_fvarId_5351_);
                        lean_dec(v___x_5350_);
                        v___x_5353_ = lean_box(0);
                        v_isShared_5354_ = v_isSharedCheck_5361_;
                        state = 39;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5345_);
                    v___x_5362_ = 1;
                    v___x_5363_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v___x_5362_,
                        v_a_5090_,
                        v_a_5091_,
                        v_a_5092_,
                        v_a_5093_,
                    );
                    return v___x_5363_;
                }
            }
            39 => {
                if v_isShared_5346_ == 0 {
                    lean_ctor_set(v___x_5345_, 0, v_fvarId_5351_);
                    v___x_5356_ = v___x_5345_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5360_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_fvarId_5351_);
                    v___x_5356_ = v_reuseFailAlloc_5360_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_5354_ == 0 {
                    lean_ctor_set(v___x_5353_, 0, v___x_5356_);
                    v___x_5358_ = v___x_5353_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5356_);
                    v___x_5358_ = v_reuseFailAlloc_5359_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5358_;
            }
            42 => {
                v___x_5369_ = l_Lean_Compiler_LCNF_toImpureType(v_type_5365_, v_a_5092_, v_a_5093_);
                if lean_obj_tag(v___x_5369_) == 0 {
                    v_a_5370_ = lean_ctor_get(v___x_5369_, 0);
                    v_isSharedCheck_5380_ = (!lean_is_exclusive(v___x_5369_)) as u8;
                    if v_isSharedCheck_5380_ == 0 {
                        v___x_5372_ = v___x_5369_;
                        v_isShared_5373_ = v_isSharedCheck_5380_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_a_5370_);
                        lean_dec(v___x_5369_);
                        v___x_5372_ = lean_box(0);
                        v_isShared_5373_ = v_isSharedCheck_5380_;
                        state = 43;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5367_);
                    v_a_5381_ = lean_ctor_get(v___x_5369_, 0);
                    v_isSharedCheck_5388_ = (!lean_is_exclusive(v___x_5369_)) as u8;
                    if v_isSharedCheck_5388_ == 0 {
                        v___x_5383_ = v___x_5369_;
                        v_isShared_5384_ = v_isSharedCheck_5388_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_a_5381_);
                        lean_dec(v___x_5369_);
                        v___x_5383_ = lean_box(0);
                        v_isShared_5384_ = v_isSharedCheck_5388_;
                        state = 46;
                        continue;
                    }
                }
            }
            43 => {
                if v_isShared_5368_ == 0 {
                    lean_ctor_set(v___x_5367_, 0, v_a_5370_);
                    v___x_5375_ = v___x_5367_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5379_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5370_);
                    v___x_5375_ = v_reuseFailAlloc_5379_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_5373_ == 0 {
                    lean_ctor_set(v___x_5372_, 0, v___x_5375_);
                    v___x_5377_ = v___x_5372_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
                    v___x_5377_ = v_reuseFailAlloc_5378_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_5377_;
            }
            46 => {
                if v_isShared_5384_ == 0 {
                    v___x_5386_ = v___x_5383_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5387_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
                    v___x_5386_ = v_reuseFailAlloc_5387_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_5386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(
    mut v_decl_5390_: *mut LeanObject,
    mut v_k_5391_: *mut LeanObject,
    mut v_ctorInfo_5392_: *mut LeanObject,
    mut v_fields_5393_: *mut LeanObject,
    mut v_irArgs_5394_: *mut LeanObject,
    mut v_i_5395_: *mut LeanObject,
    mut v_a_5396_: *mut LeanObject,
    mut v_a_5397_: *mut LeanObject,
    mut v_a_5398_: *mut LeanObject,
    mut v_a_5399_: *mut LeanObject,
    mut v_a_5400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: u8 = 0;
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5422_: u8 = 0;
    let mut v_fvarId_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5426_: u8 = 0;
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5433_: u8 = 0;
    let mut v_unused_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5437_: u8 = 0;
    let mut v_offset_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5446_: u8 = 0;
    let mut v_fvarId_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5455_: u8 = 0;
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5402_ = lean_array_get_size(v_irArgs_5394_);
                v___x_5403_ = lean_nat_dec_lt(v_i_5395_, v___x_5402_);
                if v___x_5403_ == 0 {
                    lean_dec(v_i_5395_);
                    lean_dec_ref(v_decl_5390_);
                    v___x_5404_ =
                        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                            v_k_5391_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_,
                        );
                    return v___x_5404_;
                } else {
                    v___x_5405_ = lean_array_fget_borrowed(v_irArgs_5394_, v_i_5395_);
                    if lean_obj_tag(v___x_5405_) == 0 {
                        v___x_5406_ = lean_unsigned_to_nat(1);
                        v___x_5407_ = lean_nat_add(v_i_5395_, v___x_5406_);
                        lean_dec(v_i_5395_);
                        v_i_5395_ = v___x_5407_;
                        state = 0;
                        continue;
                    } else {
                        v_fvarId_5409_ = lean_ctor_get(v___x_5405_, 0);
                        v___x_5410_ = lean_box(0);
                        v___x_5411_ =
                            lean_array_get_borrowed(v___x_5410_, v_fields_5393_, v_i_5395_);
                        match lean_obj_tag(v___x_5411_) {
                            1 => {
                                v___x_5412_ = lean_unsigned_to_nat(1);
                                v___x_5413_ = lean_nat_add(v_i_5395_, v___x_5412_);
                                lean_dec(v_i_5395_);
                                v_i_5395_ = v___x_5413_;
                                state = 0;
                                continue;
                            }
                            2 => {
                                v_i_5415_ = lean_ctor_get(v___x_5411_, 0);
                                v___x_5416_ = lean_unsigned_to_nat(1);
                                v___x_5417_ = lean_nat_add(v_i_5395_, v___x_5416_);
                                lean_dec(v_i_5395_);
                                lean_inc_ref(v_decl_5390_);
                                v___x_5418_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_5390_, v_k_5391_, v_ctorInfo_5392_, v_fields_5393_, v_irArgs_5394_, v___x_5417_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
                                if lean_obj_tag(v___x_5418_) == 0 {
                                    v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
                                    v_isSharedCheck_5437_ = (!lean_is_exclusive(v___x_5418_)) as u8;
                                    if v_isSharedCheck_5437_ == 0 {
                                        v___x_5421_ = v___x_5418_;
                                        v_isShared_5422_ = v_isSharedCheck_5437_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5419_);
                                        lean_dec(v___x_5418_);
                                        v___x_5421_ = lean_box(0);
                                        v_isShared_5422_ = v_isSharedCheck_5437_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_decl_5390_);
                                    return v___x_5418_;
                                }
                            }
                            3 => {
                                v_offset_5438_ = lean_ctor_get(v___x_5411_, 1);
                                v_type_5439_ = lean_ctor_get(v___x_5411_, 2);
                                v___x_5440_ = lean_unsigned_to_nat(1);
                                v___x_5441_ = lean_nat_add(v_i_5395_, v___x_5440_);
                                lean_dec(v_i_5395_);
                                lean_inc_ref(v_decl_5390_);
                                v___x_5442_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_5390_, v_k_5391_, v_ctorInfo_5392_, v_fields_5393_, v_irArgs_5394_, v___x_5441_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
                                if lean_obj_tag(v___x_5442_) == 0 {
                                    v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
                                    v_isSharedCheck_5455_ = (!lean_is_exclusive(v___x_5442_)) as u8;
                                    if v_isSharedCheck_5455_ == 0 {
                                        v___x_5445_ = v___x_5442_;
                                        v_isShared_5446_ = v_isSharedCheck_5455_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5443_);
                                        lean_dec(v___x_5442_);
                                        v___x_5445_ = lean_box(0);
                                        v_isShared_5446_ = v_isSharedCheck_5455_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_decl_5390_);
                                    return v___x_5442_;
                                }
                            }
                            _ => {
                                v___x_5456_ = lean_unsigned_to_nat(1);
                                v___x_5457_ = lean_nat_add(v_i_5395_, v___x_5456_);
                                lean_dec(v_i_5395_);
                                v_i_5395_ = v___x_5457_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_fvarId_5423_ = lean_ctor_get(v_decl_5390_, 0);
                v_isSharedCheck_5433_ = (!lean_is_exclusive(v_decl_5390_)) as u8;
                if v_isSharedCheck_5433_ == 0 {
                    v_unused_5434_ = lean_ctor_get(v_decl_5390_, 3);
                    lean_dec(v_unused_5434_);
                    v_unused_5435_ = lean_ctor_get(v_decl_5390_, 2);
                    lean_dec(v_unused_5435_);
                    v_unused_5436_ = lean_ctor_get(v_decl_5390_, 1);
                    lean_dec(v_unused_5436_);
                    v___x_5425_ = v_decl_5390_;
                    v_isShared_5426_ = v_isSharedCheck_5433_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fvarId_5423_);
                    lean_dec(v_decl_5390_);
                    v___x_5425_ = lean_box(0);
                    v_isShared_5426_ = v_isSharedCheck_5433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_fvarId_5409_);
                lean_inc(v_i_5415_);
                if v_isShared_5426_ == 0 {
                    lean_ctor_set_tag(v___x_5425_, 8);
                    lean_ctor_set(v___x_5425_, 3, v_a_5419_);
                    lean_ctor_set(v___x_5425_, 2, v_fvarId_5409_);
                    lean_ctor_set(v___x_5425_, 1, v_i_5415_);
                    v___x_5428_ = v___x_5425_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5432_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_fvarId_5423_);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_i_5415_);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 2, v_fvarId_5409_);
                    lean_ctor_set(v_reuseFailAlloc_5432_, 3, v_a_5419_);
                    v___x_5428_ = v_reuseFailAlloc_5432_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5422_ == 0 {
                    lean_ctor_set(v___x_5421_, 0, v___x_5428_);
                    v___x_5430_ = v___x_5421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5428_);
                    v___x_5430_ = v_reuseFailAlloc_5431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5430_;
            }
            5 => {
                v_fvarId_5447_ = lean_ctor_get(v_decl_5390_, 0);
                lean_inc(v_fvarId_5447_);
                lean_dec_ref(v_decl_5390_);
                v_size_5448_ = lean_ctor_get(v_ctorInfo_5392_, 2);
                v_usize_5449_ = lean_ctor_get(v_ctorInfo_5392_, 3);
                v___x_5450_ = lean_nat_add(v_size_5448_, v_usize_5449_);
                lean_inc_ref(v_type_5439_);
                lean_inc(v_fvarId_5409_);
                lean_inc(v_offset_5438_);
                v___x_5451_ = lean_alloc_ctor(9, 6, (0) as u32);
                lean_ctor_set(v___x_5451_, 0, v_fvarId_5447_);
                lean_ctor_set(v___x_5451_, 1, v___x_5450_);
                lean_ctor_set(v___x_5451_, 2, v_offset_5438_);
                lean_ctor_set(v___x_5451_, 3, v_fvarId_5409_);
                lean_ctor_set(v___x_5451_, 4, v_type_5439_);
                lean_ctor_set(v___x_5451_, 5, v_a_5443_);
                if v_isShared_5446_ == 0 {
                    lean_ctor_set(v___x_5445_, 0, v___x_5451_);
                    v___x_5453_ = v___x_5445_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5451_);
                    v___x_5453_ = v_reuseFailAlloc_5454_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(
    mut v_decl_5459_: *mut LeanObject,
    mut v_k_5460_: *mut LeanObject,
    mut v_ctorInfo_5461_: *mut LeanObject,
    mut v_fields_5462_: *mut LeanObject,
    mut v_irArgs_5463_: *mut LeanObject,
    mut v_a_5464_: *mut LeanObject,
    mut v_a_5465_: *mut LeanObject,
    mut v_a_5466_: *mut LeanObject,
    mut v_a_5467_: *mut LeanObject,
    mut v_a_5468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    v___x_5470_ = lean_unsigned_to_nat(0);
    v___x_5471_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_5459_, v_k_5460_, v_ctorInfo_5461_, v_fields_5462_, v_irArgs_5463_, v___x_5470_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_);
    return v___x_5471_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(
    mut v_decl_5472_: *mut LeanObject,
    mut v_k_5473_: *mut LeanObject,
    mut v_ctorInfo_5474_: *mut LeanObject,
    mut v_fields_5475_: *mut LeanObject,
    mut v_irArgs_5476_: *mut LeanObject,
    mut v_a_5477_: *mut LeanObject,
    mut v_a_5478_: *mut LeanObject,
    mut v_a_5479_: *mut LeanObject,
    mut v_a_5480_: *mut LeanObject,
    mut v_a_5481_: *mut LeanObject,
    mut v_a_5482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5483_: *mut LeanObject = core::ptr::null_mut();
    v_res_5483_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(
            v_decl_5472_,
            v_k_5473_,
            v_ctorInfo_5474_,
            v_fields_5475_,
            v_irArgs_5476_,
            v_a_5477_,
            v_a_5478_,
            v_a_5479_,
            v_a_5480_,
            v_a_5481_,
        );
    lean_dec(v_a_5481_);
    lean_dec_ref(v_a_5480_);
    lean_dec(v_a_5479_);
    lean_dec_ref(v_a_5478_);
    lean_dec(v_a_5477_);
    lean_dec_ref(v_irArgs_5476_);
    lean_dec_ref(v_fields_5475_);
    lean_dec_ref(v_ctorInfo_5474_);
    return v_res_5483_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(
    mut v_decl_5484_: *mut LeanObject,
    mut v_k_5485_: *mut LeanObject,
    mut v_name_5486_: *mut LeanObject,
    mut v_args_5487_: *mut LeanObject,
    mut v_a_5488_: *mut LeanObject,
    mut v_a_5489_: *mut LeanObject,
    mut v_a_5490_: *mut LeanObject,
    mut v_a_5491_: *mut LeanObject,
    mut v_a_5492_: *mut LeanObject,
    mut v_a_5493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5494_: *mut LeanObject = core::ptr::null_mut();
    v_res_5494_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(
        v_decl_5484_,
        v_k_5485_,
        v_name_5486_,
        v_args_5487_,
        v_a_5488_,
        v_a_5489_,
        v_a_5490_,
        v_a_5491_,
        v_a_5492_,
    );
    lean_dec(v_a_5492_);
    lean_dec_ref(v_a_5491_);
    lean_dec(v_a_5490_);
    lean_dec_ref(v_a_5489_);
    lean_dec(v_a_5488_);
    return v_res_5494_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(
    mut v_decl_5495_: *mut LeanObject,
    mut v_k_5496_: *mut LeanObject,
    mut v_name_5497_: *mut LeanObject,
    mut v_args_5498_: *mut LeanObject,
    mut v_a_5499_: *mut LeanObject,
    mut v_a_5500_: *mut LeanObject,
    mut v_a_5501_: *mut LeanObject,
    mut v_a_5502_: *mut LeanObject,
    mut v_a_5503_: *mut LeanObject,
    mut v_a_5504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5505_: *mut LeanObject = core::ptr::null_mut();
    v_res_5505_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(
        v_decl_5495_,
        v_k_5496_,
        v_name_5497_,
        v_args_5498_,
        v_a_5499_,
        v_a_5500_,
        v_a_5501_,
        v_a_5502_,
        v_a_5503_,
    );
    lean_dec(v_a_5503_);
    lean_dec_ref(v_a_5502_);
    lean_dec(v_a_5501_);
    lean_dec_ref(v_a_5500_);
    lean_dec(v_a_5499_);
    return v_res_5505_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(
    mut v_k_5506_: *mut LeanObject,
    mut v_fvarId_5507_: *mut LeanObject,
    mut v_a_5508_: *mut LeanObject,
    mut v_a_5509_: *mut LeanObject,
    mut v_a_5510_: *mut LeanObject,
    mut v_a_5511_: *mut LeanObject,
    mut v_a_5512_: *mut LeanObject,
    mut v_a_5513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5514_: *mut LeanObject = core::ptr::null_mut();
    v_res_5514_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(
            v_k_5506_,
            v_fvarId_5507_,
            v_a_5508_,
            v_a_5509_,
            v_a_5510_,
            v_a_5511_,
            v_a_5512_,
        );
    lean_dec(v_a_5512_);
    lean_dec_ref(v_a_5511_);
    lean_dec(v_a_5510_);
    lean_dec_ref(v_a_5509_);
    lean_dec(v_a_5508_);
    return v_res_5514_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(
    mut v_decl_5515_: *mut LeanObject,
    mut v_k_5516_: *mut LeanObject,
    mut v_name_5517_: *mut LeanObject,
    mut v_numParams_5518_: *mut LeanObject,
    mut v_args_5519_: *mut LeanObject,
    mut v_a_5520_: *mut LeanObject,
    mut v_a_5521_: *mut LeanObject,
    mut v_a_5522_: *mut LeanObject,
    mut v_a_5523_: *mut LeanObject,
    mut v_a_5524_: *mut LeanObject,
    mut v_a_5525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5526_: *mut LeanObject = core::ptr::null_mut();
    v_res_5526_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(
            v_decl_5515_,
            v_k_5516_,
            v_name_5517_,
            v_numParams_5518_,
            v_args_5519_,
            v_a_5520_,
            v_a_5521_,
            v_a_5522_,
            v_a_5523_,
            v_a_5524_,
        );
    lean_dec(v_a_5524_);
    lean_dec_ref(v_a_5523_);
    lean_dec(v_a_5522_);
    lean_dec_ref(v_a_5521_);
    lean_dec(v_a_5520_);
    return v_res_5526_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(
    mut v_fvarId_5527_: *mut LeanObject,
    mut v_sz_5528_: *mut LeanObject,
    mut v_i_5529_: *mut LeanObject,
    mut v_bs_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
    mut v___y_5534_: *mut LeanObject,
    mut v___y_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5537_: usize = 0;
    let mut v_i_boxed_5538_: usize = 0;
    let mut v_res_5539_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5537_ = lean_unbox_usize(v_sz_5528_);
    lean_dec(v_sz_5528_);
    v_i_boxed_5538_ = lean_unbox_usize(v_i_5529_);
    lean_dec(v_i_5529_);
    v_res_5539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_5527_, v_sz_boxed_5537_, v_i_boxed_5538_, v_bs_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_);
    lean_dec(v___y_5535_);
    lean_dec_ref(v___y_5534_);
    lean_dec(v___y_5533_);
    lean_dec_ref(v___y_5532_);
    lean_dec(v___y_5531_);
    return v_res_5539_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(
    mut v_k_5540_: *mut LeanObject,
    mut v_decl_5541_: *mut LeanObject,
    mut v_a_5542_: *mut LeanObject,
    mut v_a_5543_: *mut LeanObject,
    mut v_a_5544_: *mut LeanObject,
    mut v_a_5545_: *mut LeanObject,
    mut v_a_5546_: *mut LeanObject,
    mut v_a_5547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5548_: *mut LeanObject = core::ptr::null_mut();
    v_res_5548_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(
            v_k_5540_,
            v_decl_5541_,
            v_a_5542_,
            v_a_5543_,
            v_a_5544_,
            v_a_5545_,
            v_a_5546_,
        );
    lean_dec(v_a_5546_);
    lean_dec_ref(v_a_5545_);
    lean_dec(v_a_5544_);
    lean_dec_ref(v_a_5543_);
    lean_dec(v_a_5542_);
    return v_res_5548_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(
    mut v_discr_5549_: *mut LeanObject,
    mut v_alt_5550_: *mut LeanObject,
    mut v_a_5551_: *mut LeanObject,
    mut v_a_5552_: *mut LeanObject,
    mut v_a_5553_: *mut LeanObject,
    mut v_a_5554_: *mut LeanObject,
    mut v_a_5555_: *mut LeanObject,
    mut v_a_5556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5557_: *mut LeanObject = core::ptr::null_mut();
    v_res_5557_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(
        v_discr_5549_,
        v_alt_5550_,
        v_a_5551_,
        v_a_5552_,
        v_a_5553_,
        v_a_5554_,
        v_a_5555_,
    );
    lean_dec(v_a_5555_);
    lean_dec_ref(v_a_5554_);
    lean_dec(v_a_5553_);
    lean_dec_ref(v_a_5552_);
    lean_dec(v_a_5551_);
    return v_res_5557_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(
    mut v_decl_5558_: *mut LeanObject,
    mut v_k_5559_: *mut LeanObject,
    mut v_name_5560_: *mut LeanObject,
    mut v_numParams_5561_: *mut LeanObject,
    mut v_args_5562_: *mut LeanObject,
    mut v_a_5563_: *mut LeanObject,
    mut v_a_5564_: *mut LeanObject,
    mut v_a_5565_: *mut LeanObject,
    mut v_a_5566_: *mut LeanObject,
    mut v_a_5567_: *mut LeanObject,
    mut v_a_5568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5569_: *mut LeanObject = core::ptr::null_mut();
    v_res_5569_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(
            v_decl_5558_,
            v_k_5559_,
            v_name_5560_,
            v_numParams_5561_,
            v_args_5562_,
            v_a_5563_,
            v_a_5564_,
            v_a_5565_,
            v_a_5566_,
            v_a_5567_,
        );
    lean_dec(v_a_5567_);
    lean_dec_ref(v_a_5566_);
    lean_dec(v_a_5565_);
    lean_dec_ref(v_a_5564_);
    lean_dec(v_a_5563_);
    lean_dec_ref(v_args_5562_);
    return v_res_5569_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(
    mut v_decl_5570_: *mut LeanObject,
    mut v_k_5571_: *mut LeanObject,
    mut v_ctorInfo_5572_: *mut LeanObject,
    mut v_fields_5573_: *mut LeanObject,
    mut v_irArgs_5574_: *mut LeanObject,
    mut v_i_5575_: *mut LeanObject,
    mut v_a_5576_: *mut LeanObject,
    mut v_a_5577_: *mut LeanObject,
    mut v_a_5578_: *mut LeanObject,
    mut v_a_5579_: *mut LeanObject,
    mut v_a_5580_: *mut LeanObject,
    mut v_a_5581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5582_: *mut LeanObject = core::ptr::null_mut();
    v_res_5582_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_5570_, v_k_5571_, v_ctorInfo_5572_, v_fields_5573_, v_irArgs_5574_, v_i_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_);
    lean_dec(v_a_5580_);
    lean_dec_ref(v_a_5579_);
    lean_dec(v_a_5578_);
    lean_dec_ref(v_a_5577_);
    lean_dec(v_a_5576_);
    lean_dec_ref(v_irArgs_5574_);
    lean_dec_ref(v_fields_5573_);
    lean_dec_ref(v_ctorInfo_5572_);
    return v_res_5582_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(
    mut v_discr_5583_: *mut LeanObject,
    mut v_k_5584_: *mut LeanObject,
    mut v_ctorInfo_5585_: *mut LeanObject,
    mut v_params_5586_: *mut LeanObject,
    mut v_fields_5587_: *mut LeanObject,
    mut v_i_5588_: *mut LeanObject,
    mut v_a_5589_: *mut LeanObject,
    mut v_a_5590_: *mut LeanObject,
    mut v_a_5591_: *mut LeanObject,
    mut v_a_5592_: *mut LeanObject,
    mut v_a_5593_: *mut LeanObject,
    mut v_a_5594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5595_: *mut LeanObject = core::ptr::null_mut();
    v_res_5595_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(
        v_discr_5583_,
        v_k_5584_,
        v_ctorInfo_5585_,
        v_params_5586_,
        v_fields_5587_,
        v_i_5588_,
        v_a_5589_,
        v_a_5590_,
        v_a_5591_,
        v_a_5592_,
        v_a_5593_,
    );
    lean_dec(v_a_5593_);
    lean_dec_ref(v_a_5592_);
    lean_dec(v_a_5591_);
    lean_dec_ref(v_a_5590_);
    lean_dec(v_a_5589_);
    lean_dec_ref(v_fields_5587_);
    lean_dec_ref(v_params_5586_);
    lean_dec_ref(v_ctorInfo_5585_);
    return v_res_5595_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(
    mut v_c_5596_: *mut LeanObject,
    mut v_a_5597_: *mut LeanObject,
    mut v_a_5598_: *mut LeanObject,
    mut v_a_5599_: *mut LeanObject,
    mut v_a_5600_: *mut LeanObject,
    mut v_a_5601_: *mut LeanObject,
    mut v_a_5602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5603_: *mut LeanObject = core::ptr::null_mut();
    v_res_5603_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
        v_c_5596_, v_a_5597_, v_a_5598_, v_a_5599_, v_a_5600_, v_a_5601_,
    );
    lean_dec(v_a_5601_);
    lean_dec_ref(v_a_5600_);
    lean_dec(v_a_5599_);
    lean_dec_ref(v_a_5598_);
    lean_dec(v_a_5597_);
    return v_res_5603_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(
    mut v_decl_5604_: *mut LeanObject,
    mut v_k_5605_: *mut LeanObject,
    mut v_a_5606_: *mut LeanObject,
    mut v_a_5607_: *mut LeanObject,
    mut v_a_5608_: *mut LeanObject,
    mut v_a_5609_: *mut LeanObject,
    mut v_a_5610_: *mut LeanObject,
    mut v_a_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5612_: *mut LeanObject = core::ptr::null_mut();
    v_res_5612_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(
        v_decl_5604_,
        v_k_5605_,
        v_a_5606_,
        v_a_5607_,
        v_a_5608_,
        v_a_5609_,
        v_a_5610_,
    );
    lean_dec(v_a_5610_);
    lean_dec_ref(v_a_5609_);
    lean_dec(v_a_5608_);
    lean_dec_ref(v_a_5607_);
    lean_dec(v_a_5606_);
    return v_res_5612_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(
    mut v_00_u03b1_5613_: *mut LeanObject,
    mut v_msg_5614_: *mut LeanObject,
    mut v___y_5615_: *mut LeanObject,
    mut v___y_5616_: *mut LeanObject,
    mut v___y_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    v___x_5621_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_5614_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
    return v___x_5621_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(
    mut v_00_u03b1_5622_: *mut LeanObject,
    mut v_msg_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
    mut v___y_5628_: *mut LeanObject,
    mut v___y_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5630_: *mut LeanObject = core::ptr::null_mut();
    v_res_5630_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_5622_, v_msg_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_);
    lean_dec(v___y_5628_);
    lean_dec_ref(v___y_5627_);
    lean_dec(v___y_5626_);
    lean_dec_ref(v___y_5625_);
    lean_dec(v___y_5624_);
    return v_res_5630_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(
    mut v_sz_5631_: usize,
    mut v_i_5632_: usize,
    mut v_bs_5633_: *mut LeanObject,
    mut v___y_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    v___x_5640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_5631_, v_i_5632_, v_bs_5633_, v___y_5634_, v___y_5636_, v___y_5637_, v___y_5638_);
    return v___x_5640_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(
    mut v_sz_5641_: *mut LeanObject,
    mut v_i_5642_: *mut LeanObject,
    mut v_bs_5643_: *mut LeanObject,
    mut v___y_5644_: *mut LeanObject,
    mut v___y_5645_: *mut LeanObject,
    mut v___y_5646_: *mut LeanObject,
    mut v___y_5647_: *mut LeanObject,
    mut v___y_5648_: *mut LeanObject,
    mut v___y_5649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5650_: usize = 0;
    let mut v_i_boxed_5651_: usize = 0;
    let mut v_res_5652_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5650_ = lean_unbox_usize(v_sz_5641_);
    lean_dec(v_sz_5641_);
    v_i_boxed_5651_ = lean_unbox_usize(v_i_5642_);
    lean_dec(v_i_5642_);
    v_res_5652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_5650_, v_i_boxed_5651_, v_bs_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_);
    lean_dec(v___y_5648_);
    lean_dec_ref(v___y_5647_);
    lean_dec(v___y_5646_);
    lean_dec_ref(v___y_5645_);
    lean_dec(v___y_5644_);
    return v_res_5652_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(
    mut v_as_5653_: *mut LeanObject,
    mut v_i_5654_: usize,
    mut v_stop_5655_: usize,
    mut v_b_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    v___x_5663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_5653_, v_i_5654_, v_stop_5655_, v_b_5656_, v___y_5657_);
    return v___x_5663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(
    mut v_as_5664_: *mut LeanObject,
    mut v_i_5665_: *mut LeanObject,
    mut v_stop_5666_: *mut LeanObject,
    mut v_b_5667_: *mut LeanObject,
    mut v___y_5668_: *mut LeanObject,
    mut v___y_5669_: *mut LeanObject,
    mut v___y_5670_: *mut LeanObject,
    mut v___y_5671_: *mut LeanObject,
    mut v___y_5672_: *mut LeanObject,
    mut v___y_5673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5674_: usize = 0;
    let mut v_stop_boxed_5675_: usize = 0;
    let mut v_res_5676_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5674_ = lean_unbox_usize(v_i_5665_);
    lean_dec(v_i_5665_);
    v_stop_boxed_5675_ = lean_unbox_usize(v_stop_5666_);
    lean_dec(v_stop_5666_);
    v_res_5676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_5664_, v_i_boxed_5674_, v_stop_boxed_5675_, v_b_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
    lean_dec(v___y_5672_);
    lean_dec_ref(v___y_5671_);
    lean_dec(v___y_5670_);
    lean_dec_ref(v___y_5669_);
    lean_dec(v___y_5668_);
    lean_dec_ref(v_as_5664_);
    return v_res_5676_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(
    mut v_upperBound_5677_: *mut LeanObject,
    mut v_params_5678_: *mut LeanObject,
    mut v___x_5679_: *mut LeanObject,
    mut v_discr_5680_: *mut LeanObject,
    mut v_inst_5681_: *mut LeanObject,
    mut v_R_5682_: *mut LeanObject,
    mut v_a_5683_: *mut LeanObject,
    mut v_b_5684_: *mut LeanObject,
    mut v_c_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
    mut v___y_5690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    v___x_5692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_5677_, v_params_5678_, v___x_5679_, v_discr_5680_, v_a_5683_, v_b_5684_, v___y_5686_);
    return v___x_5692_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(
    mut v_upperBound_5693_: *mut LeanObject,
    mut v_params_5694_: *mut LeanObject,
    mut v___x_5695_: *mut LeanObject,
    mut v_discr_5696_: *mut LeanObject,
    mut v_inst_5697_: *mut LeanObject,
    mut v_R_5698_: *mut LeanObject,
    mut v_a_5699_: *mut LeanObject,
    mut v_b_5700_: *mut LeanObject,
    mut v_c_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
    mut v___y_5703_: *mut LeanObject,
    mut v___y_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
    mut v___y_5706_: *mut LeanObject,
    mut v___y_5707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5708_: *mut LeanObject = core::ptr::null_mut();
    v_res_5708_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_5693_, v_params_5694_, v___x_5695_, v_discr_5696_, v_inst_5697_, v_R_5698_, v_a_5699_, v_b_5700_, v_c_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
    lean_dec(v___y_5706_);
    lean_dec_ref(v___y_5705_);
    lean_dec(v___y_5704_);
    lean_dec_ref(v___y_5703_);
    lean_dec(v___y_5702_);
    lean_dec(v___x_5695_);
    lean_dec_ref(v_params_5694_);
    lean_dec(v_upperBound_5693_);
    return v_res_5708_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(
    mut v_sz_5709_: usize,
    mut v_i_5710_: usize,
    mut v_bs_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
    mut v___y_5714_: *mut LeanObject,
    mut v___y_5715_: *mut LeanObject,
    mut v___y_5716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    v___x_5718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_5709_, v_i_5710_, v_bs_5711_, v___y_5712_);
    return v___x_5718_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(
    mut v_sz_5719_: *mut LeanObject,
    mut v_i_5720_: *mut LeanObject,
    mut v_bs_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
    mut v___y_5727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5728_: usize = 0;
    let mut v_i_boxed_5729_: usize = 0;
    let mut v_res_5730_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5728_ = lean_unbox_usize(v_sz_5719_);
    lean_dec(v_sz_5719_);
    v_i_boxed_5729_ = lean_unbox_usize(v_i_5720_);
    lean_dec(v_i_5720_);
    v_res_5730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_5728_, v_i_boxed_5729_, v_bs_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
    lean_dec(v___y_5726_);
    lean_dec_ref(v___y_5725_);
    lean_dec(v___y_5724_);
    lean_dec_ref(v___y_5723_);
    lean_dec(v___y_5722_);
    return v_res_5730_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(
    mut v_upperBound_5731_: *mut LeanObject,
    mut v_fieldInfo_5732_: *mut LeanObject,
    mut v___x_5733_: *mut LeanObject,
    mut v_inst_5734_: *mut LeanObject,
    mut v_R_5735_: *mut LeanObject,
    mut v_a_5736_: *mut LeanObject,
    mut v_b_5737_: *mut LeanObject,
    mut v_c_5738_: *mut LeanObject,
    mut v___y_5739_: *mut LeanObject,
    mut v___y_5740_: *mut LeanObject,
    mut v___y_5741_: *mut LeanObject,
    mut v___y_5742_: *mut LeanObject,
    mut v___y_5743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    v___x_5745_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_5731_, v_fieldInfo_5732_, v___x_5733_, v_a_5736_, v_b_5737_);
    return v___x_5745_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(
    mut v_upperBound_5746_: *mut LeanObject,
    mut v_fieldInfo_5747_: *mut LeanObject,
    mut v___x_5748_: *mut LeanObject,
    mut v_inst_5749_: *mut LeanObject,
    mut v_R_5750_: *mut LeanObject,
    mut v_a_5751_: *mut LeanObject,
    mut v_b_5752_: *mut LeanObject,
    mut v_c_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
    mut v___y_5758_: *mut LeanObject,
    mut v___y_5759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5760_: *mut LeanObject = core::ptr::null_mut();
    v_res_5760_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_5746_, v_fieldInfo_5747_, v___x_5748_, v_inst_5749_, v_R_5750_, v_a_5751_, v_b_5752_, v_c_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_);
    lean_dec(v___y_5758_);
    lean_dec_ref(v___y_5757_);
    lean_dec(v___y_5756_);
    lean_dec_ref(v___y_5755_);
    lean_dec(v___y_5754_);
    lean_dec_ref(v___x_5748_);
    lean_dec_ref(v_fieldInfo_5747_);
    lean_dec(v_upperBound_5746_);
    return v_res_5760_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1()
-> *mut LeanObject {
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    v___x_5762_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0;
    v___x_5763_ = l_Lean_stringToMessageData(v___x_5762_);
    return v___x_5763_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3()
-> *mut LeanObject {
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    v___x_5765_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2;
    v___x_5766_ = l_Lean_stringToMessageData(v___x_5765_);
    return v___x_5766_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5()
-> *mut LeanObject {
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    v___x_5768_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4;
    v___x_5769_ = l_Lean_stringToMessageData(v___x_5768_);
    return v___x_5769_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7()
-> *mut LeanObject {
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    v___x_5771_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6;
    v___x_5772_ = l_Lean_stringToMessageData(v___x_5771_);
    return v___x_5772_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(
    mut v_decl_5773_: *mut LeanObject,
    mut v_a_5774_: *mut LeanObject,
    mut v_a_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
    mut v_a_5777_: *mut LeanObject,
    mut v_a_5778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_5782_: u8 = 0;
    let mut v_inlineAttr_x3f_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5786_: u8 = 0;
    let mut v_name_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_safe_5791_: u8 = 0;
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5794_: u8 = 0;
    let mut v_sz_5795_: usize = 0;
    let mut v___x_5796_: usize = 0;
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5804_: u8 = 0;
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: u8 = 0;
    let mut v_code_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5812_: u8 = 0;
    let mut v___y_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5823_: u8 = 0;
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5836_: u8 = 0;
    let mut v_a_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5844_: u8 = 0;
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5854_: u8 = 0;
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5858_: u8 = 0;
    let mut v_isSharedCheck_5859_: u8 = 0;
    let mut v_externAttrData_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5863_: u8 = 0;
    let mut v_resultType_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: u8 = 0;
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5895_: u8 = 0;
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v_isSharedCheck_5897_: u8 = 0;
    let mut v_a_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5901_: u8 = 0;
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5905_: u8 = 0;
    let mut v_a_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5909_: u8 = 0;
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5913_: u8 = 0;
    let mut v_isSharedCheck_5914_: u8 = 0;
    let mut v_isSharedCheck_5915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_5780_ = lean_ctor_get(v_decl_5773_, 0);
                v_value_5781_ = lean_ctor_get(v_decl_5773_, 1);
                v_recursive_5782_ = lean_ctor_get_uint8(
                    v_decl_5773_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_5783_ = lean_ctor_get(v_decl_5773_, 2);
                v_isSharedCheck_5915_ = (!lean_is_exclusive(v_decl_5773_)) as u8;
                if v_isSharedCheck_5915_ == 0 {
                    v___x_5785_ = v_decl_5773_;
                    v_isShared_5786_ = v_isSharedCheck_5915_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_5783_);
                    lean_inc(v_value_5781_);
                    lean_inc(v_toSignature_5780_);
                    lean_dec(v_decl_5773_);
                    v___x_5785_ = lean_box(0);
                    v_isShared_5786_ = v_isSharedCheck_5915_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_5787_ = lean_ctor_get(v_toSignature_5780_, 0);
                v_levelParams_5788_ = lean_ctor_get(v_toSignature_5780_, 1);
                v_type_5789_ = lean_ctor_get(v_toSignature_5780_, 2);
                v_params_5790_ = lean_ctor_get(v_toSignature_5780_, 3);
                v_safe_5791_ = lean_ctor_get_uint8(
                    v_toSignature_5780_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_5914_ = (!lean_is_exclusive(v_toSignature_5780_)) as u8;
                if v_isSharedCheck_5914_ == 0 {
                    v___x_5793_ = v_toSignature_5780_;
                    v_isShared_5794_ = v_isSharedCheck_5914_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_params_5790_);
                    lean_inc(v_type_5789_);
                    lean_inc(v_levelParams_5788_);
                    lean_inc(v_name_5787_);
                    lean_dec(v_toSignature_5780_);
                    v___x_5793_ = lean_box(0);
                    v_isShared_5794_ = v_isSharedCheck_5914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_5795_ = lean_array_size(v_params_5790_);
                v___x_5796_ = 0usize;
                lean_inc_ref(v_params_5790_);
                v___x_5797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_5795_, v___x_5796_, v_params_5790_, v_a_5774_, v_a_5776_, v_a_5777_, v_a_5778_);
                if lean_obj_tag(v___x_5797_) == 0 {
                    v_a_5798_ = lean_ctor_get(v___x_5797_, 0);
                    lean_inc(v_a_5798_);
                    lean_dec_ref_known(v___x_5797_, 1);
                    v___x_5799_ = lean_array_get_size(v_params_5790_);
                    lean_dec_ref(v_params_5790_);
                    v___x_5800_ = l_Lean_Compiler_LCNF_lowerResultType(
                        v_type_5789_,
                        v___x_5799_,
                        v_a_5777_,
                        v_a_5778_,
                    );
                    lean_dec_ref(v_type_5789_);
                    if lean_obj_tag(v___x_5800_) == 0 {
                        v_a_5801_ = lean_ctor_get(v___x_5800_, 0);
                        v_isSharedCheck_5897_ = (!lean_is_exclusive(v___x_5800_)) as u8;
                        if v_isSharedCheck_5897_ == 0 {
                            v___x_5803_ = v___x_5800_;
                            v_isShared_5804_ = v_isSharedCheck_5897_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5801_);
                            lean_dec(v___x_5800_);
                            v___x_5803_ = lean_box(0);
                            v_isShared_5804_ = v_isSharedCheck_5897_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5798_);
                        lean_del_object(v___x_5793_);
                        lean_dec(v_levelParams_5788_);
                        lean_dec(v_name_5787_);
                        lean_del_object(v___x_5785_);
                        lean_dec(v_inlineAttr_x3f_5783_);
                        lean_dec_ref(v_value_5781_);
                        v_a_5898_ = lean_ctor_get(v___x_5800_, 0);
                        v_isSharedCheck_5905_ = (!lean_is_exclusive(v___x_5800_)) as u8;
                        if v_isSharedCheck_5905_ == 0 {
                            v___x_5900_ = v___x_5800_;
                            v_isShared_5901_ = v_isSharedCheck_5905_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_5898_);
                            lean_dec(v___x_5800_);
                            v___x_5900_ = lean_box(0);
                            v_isShared_5901_ = v_isSharedCheck_5905_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5793_);
                    lean_dec_ref(v_params_5790_);
                    lean_dec_ref(v_type_5789_);
                    lean_dec(v_levelParams_5788_);
                    lean_dec(v_name_5787_);
                    lean_del_object(v___x_5785_);
                    lean_dec(v_inlineAttr_x3f_5783_);
                    lean_dec_ref(v_value_5781_);
                    v_a_5906_ = lean_ctor_get(v___x_5797_, 0);
                    v_isSharedCheck_5913_ = (!lean_is_exclusive(v___x_5797_)) as u8;
                    if v_isSharedCheck_5913_ == 0 {
                        v___x_5908_ = v___x_5797_;
                        v_isShared_5909_ = v_isSharedCheck_5913_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_5906_);
                        lean_dec(v___x_5797_);
                        v___x_5908_ = lean_box(0);
                        v_isShared_5909_ = v_isSharedCheck_5913_;
                        state = 25;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5805_ = lean_st_ref_get(v_a_5778_);
                v_env_5806_ = lean_ctor_get(v___x_5805_, 0);
                lean_inc_ref(v_env_5806_);
                lean_dec(v___x_5805_);
                v___x_5807_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
                lean_inc(v_name_5787_);
                v___x_5808_ = l_Lean_TagAttribute_hasTag(v___x_5807_, v_env_5806_, v_name_5787_);
                if lean_obj_tag(v_value_5781_) == 0 {
                    lean_del_object(v___x_5803_);
                    v_code_5809_ = lean_ctor_get(v_value_5781_, 0);
                    v_isSharedCheck_5859_ = (!lean_is_exclusive(v_value_5781_)) as u8;
                    if v_isSharedCheck_5859_ == 0 {
                        v___x_5811_ = v_value_5781_;
                        v_isShared_5812_ = v_isSharedCheck_5859_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_code_5809_);
                        lean_dec(v_value_5781_);
                        v___x_5811_ = lean_box(0);
                        v_isShared_5812_ = v_isSharedCheck_5859_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_externAttrData_5860_ = lean_ctor_get(v_value_5781_, 0);
                    v_isSharedCheck_5896_ = (!lean_is_exclusive(v_value_5781_)) as u8;
                    if v_isSharedCheck_5896_ == 0 {
                        v___x_5862_ = v_value_5781_;
                        v_isShared_5863_ = v_isSharedCheck_5896_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_externAttrData_5860_);
                        lean_dec(v_value_5781_);
                        v___x_5862_ = lean_box(0);
                        v_isShared_5863_ = v_isSharedCheck_5896_;
                        state = 15;
                        continue;
                    }
                }
            }
            4 => {
                if v___x_5808_ == 0 {
                    v___y_5814_ = v_a_5774_;
                    v___y_5815_ = v_a_5775_;
                    v___y_5816_ = v_a_5776_;
                    v___y_5817_ = v_a_5777_;
                    v___y_5818_ = v_a_5778_;
                    state = 5;
                    continue;
                } else {
                    lean_del_object(v___x_5811_);
                    lean_dec_ref(v_code_5809_);
                    lean_dec(v_a_5801_);
                    lean_dec(v_a_5798_);
                    lean_del_object(v___x_5793_);
                    lean_dec(v_levelParams_5788_);
                    lean_del_object(v___x_5785_);
                    lean_dec(v_inlineAttr_x3f_5783_);
                    v___x_5845_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
                    v___x_5846_ = l_Lean_MessageData_ofName(v_name_5787_);
                    v___x_5847_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5847_, 0, v___x_5845_);
                    lean_ctor_set(v___x_5847_, 1, v___x_5846_);
                    v___x_5848_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
                    v___x_5849_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5849_, 0, v___x_5847_);
                    lean_ctor_set(v___x_5849_, 1, v___x_5848_);
                    v___x_5850_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_5849_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_);
                    v_a_5851_ = lean_ctor_get(v___x_5850_, 0);
                    v_isSharedCheck_5858_ = (!lean_is_exclusive(v___x_5850_)) as u8;
                    if v_isSharedCheck_5858_ == 0 {
                        v___x_5853_ = v___x_5850_;
                        v_isShared_5854_ = v_isSharedCheck_5858_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_5851_);
                        lean_dec(v___x_5850_);
                        v___x_5853_ = lean_box(0);
                        v_isShared_5854_ = v_isSharedCheck_5858_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5819_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(
                        v_code_5809_,
                        v___y_5814_,
                        v___y_5815_,
                        v___y_5816_,
                        v___y_5817_,
                        v___y_5818_,
                    );
                if lean_obj_tag(v___x_5819_) == 0 {
                    v_a_5820_ = lean_ctor_get(v___x_5819_, 0);
                    v_isSharedCheck_5836_ = (!lean_is_exclusive(v___x_5819_)) as u8;
                    if v_isSharedCheck_5836_ == 0 {
                        v___x_5822_ = v___x_5819_;
                        v_isShared_5823_ = v_isSharedCheck_5836_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5820_);
                        lean_dec(v___x_5819_);
                        v___x_5822_ = lean_box(0);
                        v_isShared_5823_ = v_isSharedCheck_5836_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5811_);
                    lean_dec(v_a_5801_);
                    lean_dec(v_a_5798_);
                    lean_del_object(v___x_5793_);
                    lean_dec(v_levelParams_5788_);
                    lean_dec(v_name_5787_);
                    lean_del_object(v___x_5785_);
                    lean_dec(v_inlineAttr_x3f_5783_);
                    v_a_5837_ = lean_ctor_get(v___x_5819_, 0);
                    v_isSharedCheck_5844_ = (!lean_is_exclusive(v___x_5819_)) as u8;
                    if v_isSharedCheck_5844_ == 0 {
                        v___x_5839_ = v___x_5819_;
                        v_isShared_5840_ = v_isSharedCheck_5844_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5837_);
                        lean_dec(v___x_5819_);
                        v___x_5839_ = lean_box(0);
                        v_isShared_5840_ = v_isSharedCheck_5844_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5794_ == 0 {
                    lean_ctor_set(v___x_5793_, 3, v_a_5798_);
                    lean_ctor_set(v___x_5793_, 2, v_a_5801_);
                    v___x_5825_ = v___x_5793_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5835_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_name_5787_);
                    lean_ctor_set(v_reuseFailAlloc_5835_, 1, v_levelParams_5788_);
                    lean_ctor_set(v_reuseFailAlloc_5835_, 2, v_a_5801_);
                    lean_ctor_set(v_reuseFailAlloc_5835_, 3, v_a_5798_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5835_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_safe_5791_,
                    );
                    v___x_5825_ = v_reuseFailAlloc_5835_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5812_ == 0 {
                    lean_ctor_set(v___x_5811_, 0, v_a_5820_);
                    v___x_5827_ = v___x_5811_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5820_);
                    v___x_5827_ = v_reuseFailAlloc_5834_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5786_ == 0 {
                    lean_ctor_set(v___x_5785_, 1, v___x_5827_);
                    lean_ctor_set(v___x_5785_, 0, v___x_5825_);
                    v___x_5829_ = v___x_5785_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5833_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5825_);
                    lean_ctor_set(v_reuseFailAlloc_5833_, 1, v___x_5827_);
                    lean_ctor_set(v_reuseFailAlloc_5833_, 2, v_inlineAttr_x3f_5783_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5833_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_5782_,
                    );
                    v___x_5829_ = v_reuseFailAlloc_5833_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5823_ == 0 {
                    lean_ctor_set(v___x_5822_, 0, v___x_5829_);
                    v___x_5831_ = v___x_5822_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5829_);
                    v___x_5831_ = v_reuseFailAlloc_5832_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5831_;
            }
            11 => {
                if v_isShared_5840_ == 0 {
                    v___x_5842_ = v___x_5839_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_a_5837_);
                    v___x_5842_ = v_reuseFailAlloc_5843_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5842_;
            }
            13 => {
                if v_isShared_5854_ == 0 {
                    v___x_5856_ = v___x_5853_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5857_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_a_5851_);
                    v___x_5856_ = v_reuseFailAlloc_5857_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5856_;
            }
            15 => {
                if v___x_5808_ == 0 {
                    v_resultType_5865_ = v_a_5801_;
                    state = 16;
                    continue;
                } else {
                    v___x_5878_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_5801_);
                    if v___x_5878_ == 0 {
                        lean_dec(v_a_5801_);
                        v___x_5879_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
                        v_resultType_5865_ = v___x_5879_;
                        state = 16;
                        continue;
                    } else {
                        lean_del_object(v___x_5862_);
                        lean_dec(v_externAttrData_5860_);
                        lean_del_object(v___x_5803_);
                        lean_dec(v_a_5798_);
                        lean_del_object(v___x_5793_);
                        lean_dec(v_levelParams_5788_);
                        lean_del_object(v___x_5785_);
                        lean_dec(v_inlineAttr_x3f_5783_);
                        v___x_5880_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
                        v___x_5881_ = l_Lean_MessageData_ofName(v_name_5787_);
                        v___x_5882_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5882_, 0, v___x_5880_);
                        lean_ctor_set(v___x_5882_, 1, v___x_5881_);
                        v___x_5883_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
                        v___x_5884_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5884_, 0, v___x_5882_);
                        lean_ctor_set(v___x_5884_, 1, v___x_5883_);
                        v___x_5885_ = l_Lean_MessageData_ofExpr(v_a_5801_);
                        v___x_5886_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5886_, 0, v___x_5884_);
                        lean_ctor_set(v___x_5886_, 1, v___x_5885_);
                        v___x_5887_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_5886_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_);
                        v_a_5888_ = lean_ctor_get(v___x_5887_, 0);
                        v_isSharedCheck_5895_ = (!lean_is_exclusive(v___x_5887_)) as u8;
                        if v_isSharedCheck_5895_ == 0 {
                            v___x_5890_ = v___x_5887_;
                            v_isShared_5891_ = v_isSharedCheck_5895_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_5888_);
                            lean_dec(v___x_5887_);
                            v___x_5890_ = lean_box(0);
                            v_isShared_5891_ = v_isSharedCheck_5895_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            16 => {
                if v_isShared_5794_ == 0 {
                    lean_ctor_set(v___x_5793_, 3, v_a_5798_);
                    lean_ctor_set(v___x_5793_, 2, v_resultType_5865_);
                    v___x_5867_ = v___x_5793_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_name_5787_);
                    lean_ctor_set(v_reuseFailAlloc_5877_, 1, v_levelParams_5788_);
                    lean_ctor_set(v_reuseFailAlloc_5877_, 2, v_resultType_5865_);
                    lean_ctor_set(v_reuseFailAlloc_5877_, 3, v_a_5798_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5877_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_safe_5791_,
                    );
                    v___x_5867_ = v_reuseFailAlloc_5877_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5863_ == 0 {
                    v___x_5869_ = v___x_5862_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_externAttrData_5860_);
                    v___x_5869_ = v_reuseFailAlloc_5876_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_5786_ == 0 {
                    lean_ctor_set(v___x_5785_, 1, v___x_5869_);
                    lean_ctor_set(v___x_5785_, 0, v___x_5867_);
                    v___x_5871_ = v___x_5785_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 0, v___x_5867_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 1, v___x_5869_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_inlineAttr_x3f_5783_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5875_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_5782_,
                    );
                    v___x_5871_ = v_reuseFailAlloc_5875_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_5804_ == 0 {
                    lean_ctor_set(v___x_5803_, 0, v___x_5871_);
                    v___x_5873_ = v___x_5803_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5874_, 0, v___x_5871_);
                    v___x_5873_ = v_reuseFailAlloc_5874_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5873_;
            }
            21 => {
                if v_isShared_5891_ == 0 {
                    v___x_5893_ = v___x_5890_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
                    v___x_5893_ = v_reuseFailAlloc_5894_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5893_;
            }
            23 => {
                if v_isShared_5901_ == 0 {
                    v___x_5903_ = v___x_5900_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5898_);
                    v___x_5903_ = v_reuseFailAlloc_5904_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5903_;
            }
            25 => {
                if v_isShared_5909_ == 0 {
                    v___x_5911_ = v___x_5908_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5912_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5912_, 0, v_a_5906_);
                    v___x_5911_ = v_reuseFailAlloc_5912_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(
    mut v_decl_5916_: *mut LeanObject,
    mut v_a_5917_: *mut LeanObject,
    mut v_a_5918_: *mut LeanObject,
    mut v_a_5919_: *mut LeanObject,
    mut v_a_5920_: *mut LeanObject,
    mut v_a_5921_: *mut LeanObject,
    mut v_a_5922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5923_: *mut LeanObject = core::ptr::null_mut();
    v_res_5923_ =
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(
            v_decl_5916_,
            v_a_5917_,
            v_a_5918_,
            v_a_5919_,
            v_a_5920_,
            v_a_5921_,
        );
    lean_dec(v_a_5921_);
    lean_dec_ref(v_a_5920_);
    lean_dec(v_a_5919_);
    lean_dec_ref(v_a_5918_);
    lean_dec(v_a_5917_);
    return v_res_5923_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(
    mut v_decl_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
    mut v_a_5926_: *mut LeanObject,
    mut v_a_5927_: *mut LeanObject,
    mut v_a_5928_: *mut LeanObject,
    mut v_a_5929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5936_: u8 = 0;
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5940_: u8 = 0;
    let mut v_unused_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5945_: u8 = 0;
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5931_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_);
                if lean_obj_tag(v___x_5931_) == 0 {
                    v_a_5932_ = lean_ctor_get(v___x_5931_, 0);
                    lean_inc_n(v_a_5932_, 2);
                    lean_dec_ref_known(v___x_5931_, 1);
                    v___x_5933_ =
                        l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_5932_, v_a_5929_);
                    if lean_obj_tag(v___x_5933_) == 0 {
                        v_isSharedCheck_5940_ = (!lean_is_exclusive(v___x_5933_)) as u8;
                        if v_isSharedCheck_5940_ == 0 {
                            v_unused_5941_ = lean_ctor_get(v___x_5933_, 0);
                            lean_dec(v_unused_5941_);
                            v___x_5935_ = v___x_5933_;
                            v_isShared_5936_ = v_isSharedCheck_5940_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5933_);
                            v___x_5935_ = lean_box(0);
                            v_isShared_5936_ = v_isSharedCheck_5940_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5932_);
                        v_a_5942_ = lean_ctor_get(v___x_5933_, 0);
                        v_isSharedCheck_5949_ = (!lean_is_exclusive(v___x_5933_)) as u8;
                        if v_isSharedCheck_5949_ == 0 {
                            v___x_5944_ = v___x_5933_;
                            v_isShared_5945_ = v_isSharedCheck_5949_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5942_);
                            lean_dec(v___x_5933_);
                            v___x_5944_ = lean_box(0);
                            v_isShared_5945_ = v_isSharedCheck_5949_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_5931_;
                }
            }
            1 => {
                if v_isShared_5936_ == 0 {
                    lean_ctor_set(v___x_5935_, 0, v_a_5932_);
                    v___x_5938_ = v___x_5935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5939_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5939_, 0, v_a_5932_);
                    v___x_5938_ = v_reuseFailAlloc_5939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5938_;
            }
            3 => {
                if v_isShared_5945_ == 0 {
                    v___x_5947_ = v___x_5944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_a_5942_);
                    v___x_5947_ = v_reuseFailAlloc_5948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(
    mut v_decl_5950_: *mut LeanObject,
    mut v_a_5951_: *mut LeanObject,
    mut v_a_5952_: *mut LeanObject,
    mut v_a_5953_: *mut LeanObject,
    mut v_a_5954_: *mut LeanObject,
    mut v_a_5955_: *mut LeanObject,
    mut v_a_5956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5957_: *mut LeanObject = core::ptr::null_mut();
    v_res_5957_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(
        v_decl_5950_,
        v_a_5951_,
        v_a_5952_,
        v_a_5953_,
        v_a_5954_,
        v_a_5955_,
    );
    lean_dec(v_a_5955_);
    lean_dec_ref(v_a_5954_);
    lean_dec(v_a_5953_);
    lean_dec_ref(v_a_5952_);
    lean_dec(v_a_5951_);
    return v_res_5957_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0()
-> *mut LeanObject {
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    v___x_5958_ = lean_box(0);
    v___x_5959_ = lean_unsigned_to_nat(16);
    v___x_5960_ = lean_mk_array(v___x_5959_, v___x_5958_);
    return v___x_5960_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1()
-> *mut LeanObject {
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    v___x_5961_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
    v___x_5962_ = lean_unsigned_to_nat(0);
    v___x_5963_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5963_, 0, v___x_5962_);
    lean_ctor_set(v___x_5963_, 1, v___x_5961_);
    return v___x_5963_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2()
-> *mut LeanObject {
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    v___x_5964_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
    v___x_5965_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5965_, 0, v___x_5964_);
    lean_ctor_set(v___x_5965_, 1, v___x_5964_);
    return v___x_5965_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(
    mut v_decl_5966_: *mut LeanObject,
    mut v_a_5967_: *mut LeanObject,
    mut v_a_5968_: *mut LeanObject,
    mut v_a_5969_: *mut LeanObject,
    mut v_a_5970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5978_: u8 = 0;
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5972_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
                v___x_5973_ = lean_st_mk_ref(v___x_5972_);
                v___x_5974_ =
                    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(
                        v_decl_5966_,
                        v___x_5973_,
                        v_a_5967_,
                        v_a_5968_,
                        v_a_5969_,
                        v_a_5970_,
                    );
                if lean_obj_tag(v___x_5974_) == 0 {
                    v_a_5975_ = lean_ctor_get(v___x_5974_, 0);
                    v_isSharedCheck_5983_ = (!lean_is_exclusive(v___x_5974_)) as u8;
                    if v_isSharedCheck_5983_ == 0 {
                        v___x_5977_ = v___x_5974_;
                        v_isShared_5978_ = v_isSharedCheck_5983_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5975_);
                        lean_dec(v___x_5974_);
                        v___x_5977_ = lean_box(0);
                        v_isShared_5978_ = v_isSharedCheck_5983_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5973_);
                    return v___x_5974_;
                }
            }
            1 => {
                v___x_5979_ = lean_st_ref_get(v___x_5973_);
                lean_dec(v___x_5973_);
                lean_dec(v___x_5979_);
                if v_isShared_5978_ == 0 {
                    v___x_5981_ = v___x_5977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5975_);
                    v___x_5981_ = v_reuseFailAlloc_5982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(
    mut v_decl_5984_: *mut LeanObject,
    mut v_a_5985_: *mut LeanObject,
    mut v_a_5986_: *mut LeanObject,
    mut v_a_5987_: *mut LeanObject,
    mut v_a_5988_: *mut LeanObject,
    mut v_a_5989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5990_: *mut LeanObject = core::ptr::null_mut();
    v_res_5990_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(
        v_decl_5984_,
        v_a_5985_,
        v_a_5986_,
        v_a_5987_,
        v_a_5988_,
    );
    lean_dec(v_a_5988_);
    lean_dec_ref(v_a_5987_);
    lean_dec(v_a_5986_);
    lean_dec_ref(v_a_5985_);
    return v_res_5990_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(
    mut v_sz_5991_: usize,
    mut v_i_5992_: usize,
    mut v_bs_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
    mut v___y_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: usize = 0;
    let mut v___x_6007_: usize = 0;
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6013_: u8 = 0;
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5999_ = lean_usize_dec_lt(v_i_5992_, v_sz_5991_);
                if v___x_5999_ == 0 {
                    v___x_6000_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6000_, 0, v_bs_5993_);
                    return v___x_6000_;
                } else {
                    v_v_6001_ = lean_array_uget_borrowed(v_bs_5993_, v_i_5992_);
                    lean_inc(v_v_6001_);
                    v___x_6002_ =
                        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(
                            v_v_6001_,
                            v___y_5994_,
                            v___y_5995_,
                            v___y_5996_,
                            v___y_5997_,
                        );
                    if lean_obj_tag(v___x_6002_) == 0 {
                        v_a_6003_ = lean_ctor_get(v___x_6002_, 0);
                        lean_inc(v_a_6003_);
                        lean_dec_ref_known(v___x_6002_, 1);
                        v___x_6004_ = lean_unsigned_to_nat(0);
                        v_bs_x27_6005_ = lean_array_uset(v_bs_5993_, v_i_5992_, v___x_6004_);
                        v___x_6006_ = 1usize;
                        v___x_6007_ = lean_usize_add(v_i_5992_, v___x_6006_);
                        v___x_6008_ = lean_array_uset(v_bs_x27_6005_, v_i_5992_, v_a_6003_);
                        v_i_5992_ = v___x_6007_;
                        v_bs_5993_ = v___x_6008_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5993_);
                        v_a_6010_ = lean_ctor_get(v___x_6002_, 0);
                        v_isSharedCheck_6017_ = (!lean_is_exclusive(v___x_6002_)) as u8;
                        if v_isSharedCheck_6017_ == 0 {
                            v___x_6012_ = v___x_6002_;
                            v_isShared_6013_ = v_isSharedCheck_6017_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6010_);
                            lean_dec(v___x_6002_);
                            v___x_6012_ = lean_box(0);
                            v_isShared_6013_ = v_isSharedCheck_6017_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6013_ == 0 {
                    v___x_6015_ = v___x_6012_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
                    v___x_6015_ = v_reuseFailAlloc_6016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(
    mut v_sz_6018_: *mut LeanObject,
    mut v_i_6019_: *mut LeanObject,
    mut v_bs_6020_: *mut LeanObject,
    mut v___y_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
    mut v___y_6025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6026_: usize = 0;
    let mut v_i_boxed_6027_: usize = 0;
    let mut v_res_6028_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6026_ = lean_unbox_usize(v_sz_6018_);
    lean_dec(v_sz_6018_);
    v_i_boxed_6027_ = lean_unbox_usize(v_i_6019_);
    lean_dec(v_i_6019_);
    v_res_6028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_6026_, v_i_boxed_6027_, v_bs_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
    lean_dec(v___y_6024_);
    lean_dec_ref(v___y_6023_);
    lean_dec(v___y_6022_);
    lean_dec_ref(v___y_6021_);
    return v_res_6028_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toImpure___lam__0(
    mut v_x_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6035_: usize = 0;
    let mut v___x_6036_: usize = 0;
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    v_sz_6035_ = lean_array_size(v_x_6029_);
    v___x_6036_ = 0usize;
    v___x_6037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_6035_, v___x_6036_, v_x_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
    return v___x_6037_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(
    mut v_x_6038_: *mut LeanObject,
    mut v___y_6039_: *mut LeanObject,
    mut v___y_6040_: *mut LeanObject,
    mut v___y_6041_: *mut LeanObject,
    mut v___y_6042_: *mut LeanObject,
    mut v___y_6043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6044_: *mut LeanObject = core::ptr::null_mut();
    v_res_6044_ = l_Lean_Compiler_LCNF_toImpure___lam__0(
        v_x_6038_,
        v___y_6039_,
        v___y_6040_,
        v___y_6041_,
        v___y_6042_,
    );
    lean_dec(v___y_6042_);
    lean_dec_ref(v___y_6041_);
    lean_dec(v___y_6040_);
    lean_dec_ref(v___y_6039_);
    return v_res_6044_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: u8 = 0;
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    v___x_6095_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_;
    v___x_6096_ = 1;
    v___x_6097_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_;
    v___x_6098_ = l_Lean_registerTraceClass(v___x_6095_, v___x_6096_, v___x_6097_);
    return v___x_6098_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(
    mut v_a_6099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6100_: *mut LeanObject = core::ptr::null_mut();
    v_res_6100_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
    return v_res_6100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr =
        lean_io_result_get_value(res);
    lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr,
    );
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue = _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue();
    lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue);
    res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ToImpure(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ToImpure(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ToImpure(builtin);
}

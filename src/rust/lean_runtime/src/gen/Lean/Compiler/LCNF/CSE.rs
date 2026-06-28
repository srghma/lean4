// Lean compiler output
// Module: Lean.Compiler.LCNF.CSE
// Imports: Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.PassManager Lean.Compiler.NeverExtractAttr
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_get___boxed, l_StateRefT_x27_instMonad___aux__13___boxed,
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadLift___lam__0___boxed, l_instMonadLiftT___lam__0___boxed,
    l_instMonadLiftTOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Init::System::IO::{
    l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, l_instMonadEIO,
    l_instMonadLiftBaseIOEIO___lam__0___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp,
    l_Lean_Compiler_LCNF_LetValue_toExpr,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg,
    l_Lean_Compiler_LCNF_eraseFunDecl___redArg, l_Lean_Compiler_LCNF_eraseLetDecl___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, l_Lean_Compiler_LCNF_mkReturnErased,
    l_Lean_Compiler_LCNF_normFVarImp___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg, l_Lean_Compiler_LCNF_instInhabitedPass,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::ToExpr::{
    initialize_Lean_Compiler_LCNF_ToExpr, l_Lean_Compiler_LCNF_FunDecl_toExpr,
    runtime_initialize_Lean_Compiler_LCNF_ToExpr,
};
use crate::r#gen::Lean::Compiler::NeverExtractAttr::{
    initialize_Lean_Compiler_NeverExtractAttr, l_Lean_hasNeverExtractAttribute,
    runtime_initialize_Lean_Compiler_NeverExtractAttr,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_liftIOCore___boxed,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_eqv___boxed, l_Lean_Expr_hash, l_Lean_Expr_hash___boxed, l_Lean_instBEqFVarId_beq,
    l_Lean_instHashableFVarId_hash,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_liftIOCore___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftBaseIOEIO___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__12_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__11_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__10_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__14_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__15_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__8_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__16_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__7_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18_value:
    LeanClosureObject<4> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_get___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__17_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Code_cse___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Code_cse___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Code_cse___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Code_cse___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Code_cse___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Code_cse___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Code_cse___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Code_cse___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Code_cse___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Code_cse___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [99, 115, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_cse___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_cse___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value)
                as *mut LeanObject,
            12998167749957595425 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_cse___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_cse___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_cse___lam__0___closed__0_value) as *mut LeanObject,4728263101975010743 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 83, 69, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,14139838504978542981 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,14492574556649394512 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,2898251818323335721 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,5766469096258180599 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,9151084782949520458 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,321551757641286671 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,6310579810217672058 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,16803745109204125851 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,15202616333060975773 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,16288867300334980456 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,2027727582692694808 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,((( 527537415 as usize) << 1) | 1) as *mut LeanObject,1127126063760983640 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,14327045828164052767 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,8539548704535006375 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,6017976342930277970 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(
    mut v_____do__lift_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subst_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v_subst_2034_ = lean_ctor_get(v_____do__lift_2027_, 1);
    lean_inc_ref(v_subst_2034_);
    v___x_2035_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2035_, 0, v_subst_2034_);
    return v___x_2035_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0___boxed(
    mut v_____do__lift_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2043_: *mut LeanObject = core::ptr::null_mut();
    v_res_2043_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___lam__0(
        v_____do__lift_2036_,
        v___y_2037_,
        v___y_2038_,
        v___y_2039_,
        v___y_2040_,
        v___y_2041_,
    );
    lean_dec(v___y_2041_);
    lean_dec_ref(v___y_2040_);
    lean_dec(v___y_2039_);
    lean_dec_ref(v___y_2038_);
    lean_dec(v___y_2037_);
    lean_dec_ref(v_____do__lift_2036_);
    return v_res_2043_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0()
-> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_instMonadEIO(lean_box(0));
    return v___x_2044_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1()
-> *mut LeanObject {
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    v___x_2045_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__0,
    );
    v___x_2046_ = l_StateRefT_x27_instMonad___redArg(v___x_2045_);
    return v___x_2046_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse() -> *mut LeanObject {
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v_toFunctor_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___f_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v_unused_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2122_: u8 = 0;
    let mut v_unused_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2075_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__1,
                );
                v_toApplicative_2076_ = lean_ctor_get(v___x_2075_, 0);
                v_toFunctor_2077_ = lean_ctor_get(v_toApplicative_2076_, 0);
                v_toSeq_2078_ = lean_ctor_get(v_toApplicative_2076_, 2);
                v_toSeqLeft_2079_ = lean_ctor_get(v_toApplicative_2076_, 3);
                v_toSeqRight_2080_ = lean_ctor_get(v_toApplicative_2076_, 4);
                v___f_2081_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__2;
                v___f_2082_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__3;
                lean_inc_ref_n(v_toFunctor_2077_, 2);
                v___f_2083_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2083_, 0, v_toFunctor_2077_);
                v___f_2084_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2084_, 0, v_toFunctor_2077_);
                v___x_2085_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2085_, 0, v___f_2083_);
                lean_ctor_set(v___x_2085_, 1, v___f_2084_);
                lean_inc(v_toSeqRight_2080_);
                v___f_2086_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2086_, 0, v_toSeqRight_2080_);
                lean_inc(v_toSeqLeft_2079_);
                v___f_2087_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2087_, 0, v_toSeqLeft_2079_);
                lean_inc(v_toSeq_2078_);
                v___f_2088_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2088_, 0, v_toSeq_2078_);
                v___x_2089_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2089_, 0, v___x_2085_);
                lean_ctor_set(v___x_2089_, 1, v___f_2081_);
                lean_ctor_set(v___x_2089_, 2, v___f_2088_);
                lean_ctor_set(v___x_2089_, 3, v___f_2087_);
                lean_ctor_set(v___x_2089_, 4, v___f_2086_);
                v___x_2090_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2090_, 0, v___x_2089_);
                lean_ctor_set(v___x_2090_, 1, v___f_2082_);
                v___x_2091_ = l_StateRefT_x27_instMonad___redArg(v___x_2090_);
                v_toApplicative_2092_ = lean_ctor_get(v___x_2091_, 0);
                v_isSharedCheck_2122_ = (!lean_is_exclusive(v___x_2091_)) as u8;
                if v_isSharedCheck_2122_ == 0 {
                    v_unused_2123_ = lean_ctor_get(v___x_2091_, 1);
                    lean_dec(v_unused_2123_);
                    v___x_2094_ = v___x_2091_;
                    v_isShared_2095_ = v_isSharedCheck_2122_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2092_);
                    lean_dec(v___x_2091_);
                    v___x_2094_ = lean_box(0);
                    v_isShared_2095_ = v_isSharedCheck_2122_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2096_ = lean_ctor_get(v_toApplicative_2092_, 0);
                v_toSeq_2097_ = lean_ctor_get(v_toApplicative_2092_, 2);
                v_toSeqLeft_2098_ = lean_ctor_get(v_toApplicative_2092_, 3);
                v_toSeqRight_2099_ = lean_ctor_get(v_toApplicative_2092_, 4);
                v_isSharedCheck_2120_ = (!lean_is_exclusive(v_toApplicative_2092_)) as u8;
                if v_isSharedCheck_2120_ == 0 {
                    v_unused_2121_ = lean_ctor_get(v_toApplicative_2092_, 1);
                    lean_dec(v_unused_2121_);
                    v___x_2101_ = v_toApplicative_2092_;
                    v_isShared_2102_ = v_isSharedCheck_2120_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2099_);
                    lean_inc(v_toSeqLeft_2098_);
                    lean_inc(v_toSeq_2097_);
                    lean_inc(v_toFunctor_2096_);
                    lean_dec(v_toApplicative_2092_);
                    v___x_2101_ = lean_box(0);
                    v_isShared_2102_ = v_isSharedCheck_2120_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2103_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__4;
                v___f_2104_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__5;
                v___f_2105_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__6;
                lean_inc_ref(v_toFunctor_2096_);
                v___f_2106_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2106_, 0, v_toFunctor_2096_);
                v___f_2107_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2107_, 0, v_toFunctor_2096_);
                v___x_2108_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2108_, 0, v___f_2106_);
                lean_ctor_set(v___x_2108_, 1, v___f_2107_);
                v___f_2109_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2109_, 0, v_toSeqRight_2099_);
                v___f_2110_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2110_, 0, v_toSeqLeft_2098_);
                v___f_2111_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2111_, 0, v_toSeq_2097_);
                if v_isShared_2102_ == 0 {
                    lean_ctor_set(v___x_2101_, 4, v___f_2109_);
                    lean_ctor_set(v___x_2101_, 3, v___f_2110_);
                    lean_ctor_set(v___x_2101_, 2, v___f_2111_);
                    lean_ctor_set(v___x_2101_, 1, v___f_2104_);
                    lean_ctor_set(v___x_2101_, 0, v___x_2108_);
                    v___x_2113_ = v___x_2101_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2108_);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___f_2104_);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 2, v___f_2111_);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 3, v___f_2110_);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 4, v___f_2109_);
                    v___x_2113_ = v_reuseFailAlloc_2119_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2095_ == 0 {
                    lean_ctor_set(v___x_2094_, 1, v___f_2105_);
                    lean_ctor_set(v___x_2094_, 0, v___x_2113_);
                    v___x_2115_ = v___x_2094_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2113_);
                    lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___f_2105_);
                    v___x_2115_ = v_reuseFailAlloc_2118_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2116_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse___closed__18;
                v___x_2117_ = lean_alloc_closure(
                    l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
                    9,
                    8,
                );
                lean_closure_set(v___x_2117_, 0, lean_box(0));
                lean_closure_set(v___x_2117_, 1, lean_box(0));
                lean_closure_set(v___x_2117_, 2, lean_box(0));
                lean_closure_set(v___x_2117_, 3, v___x_2115_);
                lean_closure_set(v___x_2117_, 4, lean_box(0));
                lean_closure_set(v___x_2117_, 5, lean_box(0));
                lean_closure_set(v___x_2117_, 6, v___x_2116_);
                lean_closure_set(v___x_2117_, 7, v___f_2103_);
                return v___x_2117_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(
    mut v_f_2124_: *mut LeanObject,
    mut v___y_2125_: *mut LeanObject,
    mut v___y_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2136_: u8 = 0;
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2131_ = lean_st_ref_take(v___y_2125_);
                v_map_2132_ = lean_ctor_get(v___x_2131_, 0);
                v_subst_2133_ = lean_ctor_get(v___x_2131_, 1);
                v_isSharedCheck_2144_ = (!lean_is_exclusive(v___x_2131_)) as u8;
                if v_isSharedCheck_2144_ == 0 {
                    v___x_2135_ = v___x_2131_;
                    v_isShared_2136_ = v_isSharedCheck_2144_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_subst_2133_);
                    lean_inc(v_map_2132_);
                    lean_dec(v___x_2131_);
                    v___x_2135_ = lean_box(0);
                    v_isShared_2136_ = v_isSharedCheck_2144_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2137_ = lean_apply_1(v_f_2124_, v_subst_2133_);
                if v_isShared_2136_ == 0 {
                    lean_ctor_set(v___x_2135_, 1, v___x_2137_);
                    v___x_2139_ = v___x_2135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_map_2132_);
                    lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2137_);
                    v___x_2139_ = v_reuseFailAlloc_2143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2140_ = lean_st_ref_set(v___y_2125_, v___x_2139_);
                v___x_2141_ = lean_box(0);
                v___x_2142_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2142_, 0, v___x_2141_);
                return v___x_2142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0___boxed(
    mut v_f_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2152_: *mut LeanObject = core::ptr::null_mut();
    v_res_2152_ = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateMPure___lam__0(
        v_f_2145_,
        v___y_2146_,
        v___y_2147_,
        v___y_2148_,
        v___y_2149_,
        v___y_2150_,
    );
    lean_dec(v___y_2150_);
    lean_dec_ref(v___y_2149_);
    lean_dec(v___y_2148_);
    lean_dec_ref(v___y_2147_);
    lean_dec(v___y_2146_);
    return v_res_2152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_getSubst___redArg(
    mut v_a_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    v___x_2157_ = lean_st_ref_get(v_a_2155_);
    v_subst_2158_ = lean_ctor_get(v___x_2157_, 1);
    lean_inc_ref(v_subst_2158_);
    lean_dec(v___x_2157_);
    v___x_2159_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2159_, 0, v_subst_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_getSubst___redArg___boxed(
    mut v_a_2160_: *mut LeanObject,
    mut v_a_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2162_: *mut LeanObject = core::ptr::null_mut();
    v_res_2162_ = l_Lean_Compiler_LCNF_CSE_getSubst___redArg(v_a_2160_);
    lean_dec(v_a_2160_);
    return v_res_2162_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_getSubst(
    mut v_a_2163_: *mut LeanObject,
    mut v_a_2164_: *mut LeanObject,
    mut v_a_2165_: *mut LeanObject,
    mut v_a_2166_: *mut LeanObject,
    mut v_a_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    v___x_2169_ = lean_st_ref_get(v_a_2163_);
    v_subst_2170_ = lean_ctor_get(v___x_2169_, 1);
    lean_inc_ref(v_subst_2170_);
    lean_dec(v___x_2169_);
    v___x_2171_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2171_, 0, v_subst_2170_);
    return v___x_2171_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_getSubst___boxed(
    mut v_a_2172_: *mut LeanObject,
    mut v_a_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
    mut v_a_2175_: *mut LeanObject,
    mut v_a_2176_: *mut LeanObject,
    mut v_a_2177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2178_: *mut LeanObject = core::ptr::null_mut();
    v_res_2178_ =
        l_Lean_Compiler_LCNF_CSE_getSubst(v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
    lean_dec(v_a_2176_);
    lean_dec_ref(v_a_2175_);
    lean_dec(v_a_2174_);
    lean_dec_ref(v_a_2173_);
    lean_dec(v_a_2172_);
    return v_res_2178_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_addEntry___redArg(
    mut v_value_2181_: *mut LeanObject,
    mut v_fvarId_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2185_ = lean_st_ref_take(v_a_2183_);
                v_map_2186_ = lean_ctor_get(v___x_2185_, 0);
                v_subst_2187_ = lean_ctor_get(v___x_2185_, 1);
                v_isSharedCheck_2200_ = (!lean_is_exclusive(v___x_2185_)) as u8;
                if v_isSharedCheck_2200_ == 0 {
                    v___x_2189_ = v___x_2185_;
                    v_isShared_2190_ = v_isSharedCheck_2200_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_subst_2187_);
                    lean_inc(v_map_2186_);
                    lean_dec(v___x_2185_);
                    v___x_2189_ = lean_box(0);
                    v_isShared_2190_ = v_isSharedCheck_2200_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2191_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
                v___x_2192_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
                v___x_2193_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___x_2191_,
                    v___x_2192_,
                    v_map_2186_,
                    v_value_2181_,
                    v_fvarId_2182_,
                );
                if v_isShared_2190_ == 0 {
                    lean_ctor_set(v___x_2189_, 0, v___x_2193_);
                    v___x_2195_ = v___x_2189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2193_);
                    lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_subst_2187_);
                    v___x_2195_ = v_reuseFailAlloc_2199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2196_ = lean_st_ref_set(v_a_2183_, v___x_2195_);
                v___x_2197_ = lean_box(0);
                v___x_2198_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2198_, 0, v___x_2197_);
                return v___x_2198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_addEntry___redArg___boxed(
    mut v_value_2201_: *mut LeanObject,
    mut v_fvarId_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2205_: *mut LeanObject = core::ptr::null_mut();
    v_res_2205_ =
        l_Lean_Compiler_LCNF_CSE_addEntry___redArg(v_value_2201_, v_fvarId_2202_, v_a_2203_);
    lean_dec(v_a_2203_);
    return v_res_2205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_addEntry(
    mut v_value_2206_: *mut LeanObject,
    mut v_fvarId_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
    mut v_a_2209_: *mut LeanObject,
    mut v_a_2210_: *mut LeanObject,
    mut v_a_2211_: *mut LeanObject,
    mut v_a_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2214_ = lean_st_ref_take(v_a_2208_);
                v_map_2215_ = lean_ctor_get(v___x_2214_, 0);
                v_subst_2216_ = lean_ctor_get(v___x_2214_, 1);
                v_isSharedCheck_2229_ = (!lean_is_exclusive(v___x_2214_)) as u8;
                if v_isSharedCheck_2229_ == 0 {
                    v___x_2218_ = v___x_2214_;
                    v_isShared_2219_ = v_isSharedCheck_2229_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_subst_2216_);
                    lean_inc(v_map_2215_);
                    lean_dec(v___x_2214_);
                    v___x_2218_ = lean_box(0);
                    v_isShared_2219_ = v_isSharedCheck_2229_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2220_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__0;
                v___x_2221_ = l_Lean_Compiler_LCNF_CSE_addEntry___redArg___closed__1;
                v___x_2222_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___x_2220_,
                    v___x_2221_,
                    v_map_2215_,
                    v_value_2206_,
                    v_fvarId_2207_,
                );
                if v_isShared_2219_ == 0 {
                    lean_ctor_set(v___x_2218_, 0, v___x_2222_);
                    v___x_2224_ = v___x_2218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2222_);
                    lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_subst_2216_);
                    v___x_2224_ = v_reuseFailAlloc_2228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2225_ = lean_st_ref_set(v_a_2208_, v___x_2224_);
                v___x_2226_ = lean_box(0);
                v___x_2227_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2227_, 0, v___x_2226_);
                return v___x_2227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_addEntry___boxed(
    mut v_value_2230_: *mut LeanObject,
    mut v_fvarId_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
    mut v_a_2233_: *mut LeanObject,
    mut v_a_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
    mut v_a_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2238_: *mut LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Lean_Compiler_LCNF_CSE_addEntry(
        v_value_2230_,
        v_fvarId_2231_,
        v_a_2232_,
        v_a_2233_,
        v_a_2234_,
        v_a_2235_,
        v_a_2236_,
    );
    lean_dec(v_a_2236_);
    lean_dec_ref(v_a_2235_);
    lean_dec(v_a_2234_);
    lean_dec_ref(v_a_2233_);
    lean_dec(v_a_2232_);
    return v_res_2238_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(
    mut v_a_2239_: *mut LeanObject,
    mut v_map_2240_: *mut LeanObject,
    mut v_a_x3f_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2247_: u8 = 0;
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut v_unused_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2243_ = lean_st_ref_take(v_a_2239_);
                v_subst_2244_ = lean_ctor_get(v___x_2243_, 1);
                v_isSharedCheck_2254_ = (!lean_is_exclusive(v___x_2243_)) as u8;
                if v_isSharedCheck_2254_ == 0 {
                    v_unused_2255_ = lean_ctor_get(v___x_2243_, 0);
                    lean_dec(v_unused_2255_);
                    v___x_2246_ = v___x_2243_;
                    v_isShared_2247_ = v_isSharedCheck_2254_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_subst_2244_);
                    lean_dec(v___x_2243_);
                    v___x_2246_ = lean_box(0);
                    v_isShared_2247_ = v_isSharedCheck_2254_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2247_ == 0 {
                    lean_ctor_set(v___x_2246_, 0, v_map_2240_);
                    v___x_2249_ = v___x_2246_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_map_2240_);
                    lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_subst_2244_);
                    v___x_2249_ = v_reuseFailAlloc_2253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2250_ = lean_st_ref_set(v_a_2239_, v___x_2249_);
                v___x_2251_ = lean_box(0);
                v___x_2252_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2252_, 0, v___x_2251_);
                return v___x_2252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0___boxed(
    mut v_a_2256_: *mut LeanObject,
    mut v_map_2257_: *mut LeanObject,
    mut v_a_x3f_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2260_: *mut LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(
        v_a_2256_,
        v_map_2257_,
        v_a_x3f_2258_,
    );
    lean_dec(v_a_x3f_2258_);
    lean_dec(v_a_2256_);
    return v_res_2260_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(
    mut v_x_2261_: *mut LeanObject,
    mut v_a_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v_unused_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut v_a_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_unused_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2268_ = lean_st_ref_get(v_a_2262_);
                v_map_2269_ = lean_ctor_get(v___x_2268_, 0);
                lean_inc_ref(v_map_2269_);
                lean_dec(v___x_2268_);
                lean_inc(v_a_2266_);
                lean_inc_ref(v_a_2265_);
                lean_inc(v_a_2264_);
                lean_inc_ref(v_a_2263_);
                lean_inc(v_a_2262_);
                v_r_2270_ = lean_apply_6(
                    v_x_2261_,
                    v_a_2262_,
                    v_a_2263_,
                    v_a_2264_,
                    v_a_2265_,
                    v_a_2266_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_2270_) == 0 {
                    v_a_2271_ = lean_ctor_get(v_r_2270_, 0);
                    v_isSharedCheck_2287_ = (!lean_is_exclusive(v_r_2270_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2273_ = v_r_2270_;
                        v_isShared_2274_ = v_isSharedCheck_2287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2271_);
                        lean_dec(v_r_2270_);
                        v___x_2273_ = lean_box(0);
                        v_isShared_2274_ = v_isSharedCheck_2287_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2288_ = lean_ctor_get(v_r_2270_, 0);
                    lean_inc(v_a_2288_);
                    lean_dec_ref_known(v_r_2270_, 1);
                    v___x_2289_ = lean_box(0);
                    v___x_2290_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(
                        v_a_2262_,
                        v_map_2269_,
                        v___x_2289_,
                    );
                    v_isSharedCheck_2297_ = (!lean_is_exclusive(v___x_2290_)) as u8;
                    if v_isSharedCheck_2297_ == 0 {
                        v_unused_2298_ = lean_ctor_get(v___x_2290_, 0);
                        lean_dec(v_unused_2298_);
                        v___x_2292_ = v___x_2290_;
                        v_isShared_2293_ = v_isSharedCheck_2297_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_2290_);
                        v___x_2292_ = lean_box(0);
                        v_isShared_2293_ = v_isSharedCheck_2297_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_2271_);
                if v_isShared_2274_ == 0 {
                    lean_ctor_set_tag(v___x_2273_, 1);
                    v___x_2276_ = v___x_2273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2277_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(
                    v_a_2262_,
                    v_map_2269_,
                    v___x_2276_,
                );
                lean_dec_ref(v___x_2276_);
                v_isSharedCheck_2284_ = (!lean_is_exclusive(v___x_2277_)) as u8;
                if v_isSharedCheck_2284_ == 0 {
                    v_unused_2285_ = lean_ctor_get(v___x_2277_, 0);
                    lean_dec(v_unused_2285_);
                    v___x_2279_ = v___x_2277_;
                    v_isShared_2280_ = v_isSharedCheck_2284_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_2277_);
                    v___x_2279_ = lean_box(0);
                    v_isShared_2280_ = v_isSharedCheck_2284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2280_ == 0 {
                    lean_ctor_set(v___x_2279_, 0, v_a_2271_);
                    v___x_2282_ = v___x_2279_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2271_);
                    v___x_2282_ = v_reuseFailAlloc_2283_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2282_;
            }
            5 => {
                if v_isShared_2293_ == 0 {
                    lean_ctor_set_tag(v___x_2292_, 1);
                    lean_ctor_set(v___x_2292_, 0, v_a_2288_);
                    v___x_2295_ = v___x_2292_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2288_);
                    v___x_2295_ = v_reuseFailAlloc_2296_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___boxed(
    mut v_x_2299_: *mut LeanObject,
    mut v_a_2300_: *mut LeanObject,
    mut v_a_2301_: *mut LeanObject,
    mut v_a_2302_: *mut LeanObject,
    mut v_a_2303_: *mut LeanObject,
    mut v_a_2304_: *mut LeanObject,
    mut v_a_2305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2306_: *mut LeanObject = core::ptr::null_mut();
    v_res_2306_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg(
        v_x_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_,
    );
    lean_dec(v_a_2304_);
    lean_dec_ref(v_a_2303_);
    lean_dec(v_a_2302_);
    lean_dec_ref(v_a_2301_);
    lean_dec(v_a_2300_);
    return v_res_2306_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_withNewScope(
    mut v_00_u03b1_2307_: *mut LeanObject,
    mut v_x_2308_: *mut LeanObject,
    mut v_a_2309_: *mut LeanObject,
    mut v_a_2310_: *mut LeanObject,
    mut v_a_2311_: *mut LeanObject,
    mut v_a_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_unused_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut v_a_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut v_unused_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2315_ = lean_st_ref_get(v_a_2309_);
                v_map_2316_ = lean_ctor_get(v___x_2315_, 0);
                lean_inc_ref(v_map_2316_);
                lean_dec(v___x_2315_);
                lean_inc(v_a_2313_);
                lean_inc_ref(v_a_2312_);
                lean_inc(v_a_2311_);
                lean_inc_ref(v_a_2310_);
                lean_inc(v_a_2309_);
                v_r_2317_ = lean_apply_6(
                    v_x_2308_,
                    v_a_2309_,
                    v_a_2310_,
                    v_a_2311_,
                    v_a_2312_,
                    v_a_2313_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_2317_) == 0 {
                    v_a_2318_ = lean_ctor_get(v_r_2317_, 0);
                    v_isSharedCheck_2334_ = (!lean_is_exclusive(v_r_2317_)) as u8;
                    if v_isSharedCheck_2334_ == 0 {
                        v___x_2320_ = v_r_2317_;
                        v_isShared_2321_ = v_isSharedCheck_2334_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2318_);
                        lean_dec(v_r_2317_);
                        v___x_2320_ = lean_box(0);
                        v_isShared_2321_ = v_isSharedCheck_2334_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2335_ = lean_ctor_get(v_r_2317_, 0);
                    lean_inc(v_a_2335_);
                    lean_dec_ref_known(v_r_2317_, 1);
                    v___x_2336_ = lean_box(0);
                    v___x_2337_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(
                        v_a_2309_,
                        v_map_2316_,
                        v___x_2336_,
                    );
                    v_isSharedCheck_2344_ = (!lean_is_exclusive(v___x_2337_)) as u8;
                    if v_isSharedCheck_2344_ == 0 {
                        v_unused_2345_ = lean_ctor_get(v___x_2337_, 0);
                        lean_dec(v_unused_2345_);
                        v___x_2339_ = v___x_2337_;
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_2337_);
                        v___x_2339_ = lean_box(0);
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_2318_);
                if v_isShared_2321_ == 0 {
                    lean_ctor_set_tag(v___x_2320_, 1);
                    v___x_2323_ = v___x_2320_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2318_);
                    v___x_2323_ = v_reuseFailAlloc_2333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2324_ = l_Lean_Compiler_LCNF_CSE_withNewScope___redArg___lam__0(
                    v_a_2309_,
                    v_map_2316_,
                    v___x_2323_,
                );
                lean_dec_ref(v___x_2323_);
                v_isSharedCheck_2331_ = (!lean_is_exclusive(v___x_2324_)) as u8;
                if v_isSharedCheck_2331_ == 0 {
                    v_unused_2332_ = lean_ctor_get(v___x_2324_, 0);
                    lean_dec(v_unused_2332_);
                    v___x_2326_ = v___x_2324_;
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_2324_);
                    v___x_2326_ = lean_box(0);
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2327_ == 0 {
                    lean_ctor_set(v___x_2326_, 0, v_a_2318_);
                    v___x_2329_ = v___x_2326_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2318_);
                    v___x_2329_ = v_reuseFailAlloc_2330_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2329_;
            }
            5 => {
                if v_isShared_2340_ == 0 {
                    lean_ctor_set_tag(v___x_2339_, 1);
                    lean_ctor_set(v___x_2339_, 0, v_a_2335_);
                    v___x_2342_ = v___x_2339_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2335_);
                    v___x_2342_ = v_reuseFailAlloc_2343_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_withNewScope___boxed(
    mut v_00_u03b1_2346_: *mut LeanObject,
    mut v_x_2347_: *mut LeanObject,
    mut v_a_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
    mut v_a_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2354_: *mut LeanObject = core::ptr::null_mut();
    v_res_2354_ = l_Lean_Compiler_LCNF_CSE_withNewScope(
        v_00_u03b1_2346_,
        v_x_2347_,
        v_a_2348_,
        v_a_2349_,
        v_a_2350_,
        v_a_2351_,
        v_a_2352_,
    );
    lean_dec(v_a_2352_);
    lean_dec_ref(v_a_2351_);
    lean_dec(v_a_2350_);
    lean_dec_ref(v_a_2349_);
    lean_dec(v_a_2348_);
    return v_res_2354_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_2355_: *mut LeanObject,
    mut v_x_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: u64 = 0;
    let mut v___x_2365_: u64 = 0;
    let mut v___x_2366_: u64 = 0;
    let mut v_fold_2367_: u64 = 0;
    let mut v___x_2368_: u64 = 0;
    let mut v___x_2369_: u64 = 0;
    let mut v___x_2370_: u64 = 0;
    let mut v___x_2371_: usize = 0;
    let mut v___x_2372_: usize = 0;
    let mut v___x_2373_: usize = 0;
    let mut v___x_2374_: usize = 0;
    let mut v___x_2375_: usize = 0;
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2356_) == 0 {
                    return v_x_2355_;
                } else {
                    v_key_2357_ = lean_ctor_get(v_x_2356_, 0);
                    v_value_2358_ = lean_ctor_get(v_x_2356_, 1);
                    v_tail_2359_ = lean_ctor_get(v_x_2356_, 2);
                    v_isSharedCheck_2382_ = (!lean_is_exclusive(v_x_2356_)) as u8;
                    if v_isSharedCheck_2382_ == 0 {
                        v___x_2361_ = v_x_2356_;
                        v_isShared_2362_ = v_isSharedCheck_2382_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2359_);
                        lean_inc(v_value_2358_);
                        lean_inc(v_key_2357_);
                        lean_dec(v_x_2356_);
                        v___x_2361_ = lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2382_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2363_ = lean_array_get_size(v_x_2355_);
                v___x_2364_ = l_Lean_instHashableFVarId_hash(v_key_2357_);
                v___x_2365_ = 32u64;
                v___x_2366_ = lean_uint64_shift_right(v___x_2364_, v___x_2365_);
                v_fold_2367_ = lean_uint64_xor(v___x_2364_, v___x_2366_);
                v___x_2368_ = 16u64;
                v___x_2369_ = lean_uint64_shift_right(v_fold_2367_, v___x_2368_);
                v___x_2370_ = lean_uint64_xor(v_fold_2367_, v___x_2369_);
                v___x_2371_ = lean_uint64_to_usize(v___x_2370_);
                v___x_2372_ = lean_usize_of_nat(v___x_2363_);
                v___x_2373_ = 1usize;
                v___x_2374_ = lean_usize_sub(v___x_2372_, v___x_2373_);
                v___x_2375_ = lean_usize_land(v___x_2371_, v___x_2374_);
                v___x_2376_ = lean_array_uget_borrowed(v_x_2355_, v___x_2375_);
                lean_inc(v___x_2376_);
                if v_isShared_2362_ == 0 {
                    lean_ctor_set(v___x_2361_, 2, v___x_2376_);
                    v___x_2378_ = v___x_2361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_key_2357_);
                    lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_value_2358_);
                    lean_ctor_set(v_reuseFailAlloc_2381_, 2, v___x_2376_);
                    v___x_2378_ = v_reuseFailAlloc_2381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2379_ = lean_array_uset(v_x_2355_, v___x_2375_, v___x_2378_);
                v_x_2355_ = v___x_2379_;
                v_x_2356_ = v_tail_2359_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(
    mut v_i_2383_: *mut LeanObject,
    mut v_source_2384_: *mut LeanObject,
    mut v_target_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v_es_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2386_ = lean_array_get_size(v_source_2384_);
                v___x_2387_ = lean_nat_dec_lt(v_i_2383_, v___x_2386_);
                if v___x_2387_ == 0 {
                    lean_dec_ref(v_source_2384_);
                    lean_dec(v_i_2383_);
                    return v_target_2385_;
                } else {
                    v_es_2388_ = lean_array_fget(v_source_2384_, v_i_2383_);
                    v___x_2389_ = lean_box(0);
                    v_source_2390_ = lean_array_fset(v_source_2384_, v_i_2383_, v___x_2389_);
                    v_target_2391_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2385_, v_es_2388_);
                    v___x_2392_ = lean_unsigned_to_nat(1);
                    v___x_2393_ = lean_nat_add(v_i_2383_, v___x_2392_);
                    lean_dec(v_i_2383_);
                    v_i_2383_ = v___x_2393_;
                    v_source_2384_ = v_source_2390_;
                    v_target_2385_ = v_target_2391_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(
    mut v_data_2395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    v___x_2396_ = lean_array_get_size(v_data_2395_);
    v___x_2397_ = lean_unsigned_to_nat(2);
    v_nbuckets_2398_ = lean_nat_mul(v___x_2396_, v___x_2397_);
    v___x_2399_ = lean_unsigned_to_nat(0);
    v___x_2400_ = lean_box(0);
    v___x_2401_ = lean_mk_array(v_nbuckets_2398_, v___x_2400_);
    v___x_2402_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v___x_2399_, v_data_2395_, v___x_2401_);
    return v___x_2402_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(
    mut v_a_2403_: *mut LeanObject,
    mut v_b_2404_: *mut LeanObject,
    mut v_x_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___x_2412_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2405_) == 0 {
                    lean_dec(v_b_2404_);
                    lean_dec(v_a_2403_);
                    return v_x_2405_;
                } else {
                    v_key_2406_ = lean_ctor_get(v_x_2405_, 0);
                    v_value_2407_ = lean_ctor_get(v_x_2405_, 1);
                    v_tail_2408_ = lean_ctor_get(v_x_2405_, 2);
                    v_isSharedCheck_2420_ = (!lean_is_exclusive(v_x_2405_)) as u8;
                    if v_isSharedCheck_2420_ == 0 {
                        v___x_2410_ = v_x_2405_;
                        v_isShared_2411_ = v_isSharedCheck_2420_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2408_);
                        lean_inc(v_value_2407_);
                        lean_inc(v_key_2406_);
                        lean_dec(v_x_2405_);
                        v___x_2410_ = lean_box(0);
                        v_isShared_2411_ = v_isSharedCheck_2420_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2412_ = l_Lean_instBEqFVarId_beq(v_key_2406_, v_a_2403_);
                if v___x_2412_ == 0 {
                    v___x_2413_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_2403_, v_b_2404_, v_tail_2408_);
                    if v_isShared_2411_ == 0 {
                        lean_ctor_set(v___x_2410_, 2, v___x_2413_);
                        v___x_2415_ = v___x_2410_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_key_2406_);
                        lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_value_2407_);
                        lean_ctor_set(v_reuseFailAlloc_2416_, 2, v___x_2413_);
                        v___x_2415_ = v_reuseFailAlloc_2416_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2407_);
                    lean_dec(v_key_2406_);
                    if v_isShared_2411_ == 0 {
                        lean_ctor_set(v___x_2410_, 1, v_b_2404_);
                        lean_ctor_set(v___x_2410_, 0, v_a_2403_);
                        v___x_2418_ = v___x_2410_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2403_);
                        lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_b_2404_);
                        lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_tail_2408_);
                        v___x_2418_ = v_reuseFailAlloc_2419_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2415_;
            }
            3 => {
                return v___x_2418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(
    mut v_a_2421_: *mut LeanObject,
    mut v_x_2422_: *mut LeanObject,
) -> u8 {
    let mut v___x_2423_: u8 = 0;
    let mut v_key_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2422_) == 0 {
                    v___x_2423_ = 0;
                    return v___x_2423_;
                } else {
                    v_key_2424_ = lean_ctor_get(v_x_2422_, 0);
                    v_tail_2425_ = lean_ctor_get(v_x_2422_, 2);
                    v___x_2426_ = l_Lean_instBEqFVarId_beq(v_key_2424_, v_a_2421_);
                    if v___x_2426_ == 0 {
                        v_x_2422_ = v_tail_2425_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2426_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg___boxed(
    mut v_a_2428_: *mut LeanObject,
    mut v_x_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2430_: u8 = 0;
    let mut v_r_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2430_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_2428_, v_x_2429_);
    lean_dec(v_x_2429_);
    lean_dec(v_a_2428_);
    v_r_2431_ = lean_box((v_res_2430_) as usize);
    return v_r_2431_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(
    mut v_m_2432_: *mut LeanObject,
    mut v_a_2433_: *mut LeanObject,
    mut v_b_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2439_: u8 = 0;
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u64 = 0;
    let mut v___x_2442_: u64 = 0;
    let mut v___x_2443_: u64 = 0;
    let mut v_fold_2444_: u64 = 0;
    let mut v___x_2445_: u64 = 0;
    let mut v___x_2446_: u64 = 0;
    let mut v___x_2447_: u64 = 0;
    let mut v___x_2448_: usize = 0;
    let mut v___x_2449_: usize = 0;
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: usize = 0;
    let mut v_bkt_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u8 = 0;
    let mut v_val_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2435_ = lean_ctor_get(v_m_2432_, 0);
                v_buckets_2436_ = lean_ctor_get(v_m_2432_, 1);
                v_isSharedCheck_2479_ = (!lean_is_exclusive(v_m_2432_)) as u8;
                if v_isSharedCheck_2479_ == 0 {
                    v___x_2438_ = v_m_2432_;
                    v_isShared_2439_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2436_);
                    lean_inc(v_size_2435_);
                    lean_dec(v_m_2432_);
                    v___x_2438_ = lean_box(0);
                    v_isShared_2439_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2440_ = lean_array_get_size(v_buckets_2436_);
                v___x_2441_ = l_Lean_instHashableFVarId_hash(v_a_2433_);
                v___x_2442_ = 32u64;
                v___x_2443_ = lean_uint64_shift_right(v___x_2441_, v___x_2442_);
                v_fold_2444_ = lean_uint64_xor(v___x_2441_, v___x_2443_);
                v___x_2445_ = 16u64;
                v___x_2446_ = lean_uint64_shift_right(v_fold_2444_, v___x_2445_);
                v___x_2447_ = lean_uint64_xor(v_fold_2444_, v___x_2446_);
                v___x_2448_ = lean_uint64_to_usize(v___x_2447_);
                v___x_2449_ = lean_usize_of_nat(v___x_2440_);
                v___x_2450_ = 1usize;
                v___x_2451_ = lean_usize_sub(v___x_2449_, v___x_2450_);
                v___x_2452_ = lean_usize_land(v___x_2448_, v___x_2451_);
                v_bkt_2453_ = lean_array_uget_borrowed(v_buckets_2436_, v___x_2452_);
                v___x_2454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_2433_, v_bkt_2453_);
                if v___x_2454_ == 0 {
                    v___x_2455_ = lean_unsigned_to_nat(1);
                    v_size_x27_2456_ = lean_nat_add(v_size_2435_, v___x_2455_);
                    lean_dec(v_size_2435_);
                    lean_inc(v_bkt_2453_);
                    v___x_2457_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2457_, 0, v_a_2433_);
                    lean_ctor_set(v___x_2457_, 1, v_b_2434_);
                    lean_ctor_set(v___x_2457_, 2, v_bkt_2453_);
                    v_buckets_x27_2458_ =
                        lean_array_uset(v_buckets_2436_, v___x_2452_, v___x_2457_);
                    v___x_2459_ = lean_unsigned_to_nat(4);
                    v___x_2460_ = lean_nat_mul(v_size_x27_2456_, v___x_2459_);
                    v___x_2461_ = lean_unsigned_to_nat(3);
                    v___x_2462_ = lean_nat_div(v___x_2460_, v___x_2461_);
                    lean_dec(v___x_2460_);
                    v___x_2463_ = lean_array_get_size(v_buckets_x27_2458_);
                    v___x_2464_ = lean_nat_dec_le(v___x_2462_, v___x_2463_);
                    lean_dec(v___x_2462_);
                    if v___x_2464_ == 0 {
                        v_val_2465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_buckets_x27_2458_);
                        if v_isShared_2439_ == 0 {
                            lean_ctor_set(v___x_2438_, 1, v_val_2465_);
                            lean_ctor_set(v___x_2438_, 0, v_size_x27_2456_);
                            v___x_2467_ = v___x_2438_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_size_x27_2456_);
                            lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_val_2465_);
                            v___x_2467_ = v_reuseFailAlloc_2468_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2439_ == 0 {
                            lean_ctor_set(v___x_2438_, 1, v_buckets_x27_2458_);
                            lean_ctor_set(v___x_2438_, 0, v_size_x27_2456_);
                            v___x_2470_ = v___x_2438_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_size_x27_2456_);
                            lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_buckets_x27_2458_);
                            v___x_2470_ = v_reuseFailAlloc_2471_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2453_);
                    v___x_2472_ = lean_box(0);
                    v_buckets_x27_2473_ =
                        lean_array_uset(v_buckets_2436_, v___x_2452_, v___x_2472_);
                    v___x_2474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_2433_, v_b_2434_, v_bkt_2453_);
                    v___x_2475_ = lean_array_uset(v_buckets_x27_2473_, v___x_2452_, v___x_2474_);
                    if v_isShared_2439_ == 0 {
                        lean_ctor_set(v___x_2438_, 1, v___x_2475_);
                        v___x_2477_ = v___x_2438_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_size_2435_);
                        lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2475_);
                        v___x_2477_ = v_reuseFailAlloc_2478_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2467_;
            }
            3 => {
                return v___x_2470_;
            }
            4 => {
                return v___x_2477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(
    mut v_decl_2480_: *mut LeanObject,
    mut v_fvarId_2481_: *mut LeanObject,
    mut v_a_2482_: *mut LeanObject,
    mut v_a_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut v_unused_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2485_ = 0;
                v___x_2486_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                    v___x_2485_,
                    v_decl_2480_,
                    v_a_2483_,
                );
                if lean_obj_tag(v___x_2486_) == 0 {
                    v_isSharedCheck_2508_ = (!lean_is_exclusive(v___x_2486_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v_unused_2509_ = lean_ctor_get(v___x_2486_, 0);
                        lean_dec(v_unused_2509_);
                        v___x_2488_ = v___x_2486_;
                        v_isShared_2489_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2486_);
                        v___x_2488_ = lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fvarId_2481_);
                    lean_dec_ref(v_decl_2480_);
                    return v___x_2486_;
                }
            }
            1 => {
                v___x_2490_ = lean_st_ref_take(v_a_2482_);
                v_fvarId_2491_ = lean_ctor_get(v_decl_2480_, 0);
                lean_inc(v_fvarId_2491_);
                lean_dec_ref(v_decl_2480_);
                v_map_2492_ = lean_ctor_get(v___x_2490_, 0);
                v_subst_2493_ = lean_ctor_get(v___x_2490_, 1);
                v_isSharedCheck_2507_ = (!lean_is_exclusive(v___x_2490_)) as u8;
                if v_isSharedCheck_2507_ == 0 {
                    v___x_2495_ = v___x_2490_;
                    v_isShared_2496_ = v_isSharedCheck_2507_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_subst_2493_);
                    lean_inc(v_map_2492_);
                    lean_dec(v___x_2490_);
                    v___x_2495_ = lean_box(0);
                    v_isShared_2496_ = v_isSharedCheck_2507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2497_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2497_, 0, v_fvarId_2481_);
                v___x_2498_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_2493_, v_fvarId_2491_, v___x_2497_);
                if v_isShared_2496_ == 0 {
                    lean_ctor_set(v___x_2495_, 1, v___x_2498_);
                    v___x_2500_ = v___x_2495_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_map_2492_);
                    lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2498_);
                    v___x_2500_ = v_reuseFailAlloc_2506_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2501_ = lean_st_ref_set(v_a_2482_, v___x_2500_);
                v___x_2502_ = lean_box(0);
                if v_isShared_2489_ == 0 {
                    lean_ctor_set(v___x_2488_, 0, v___x_2502_);
                    v___x_2504_ = v___x_2488_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
                    v___x_2504_ = v_reuseFailAlloc_2505_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceLet___redArg___boxed(
    mut v_decl_2510_: *mut LeanObject,
    mut v_fvarId_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2515_: *mut LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(
        v_decl_2510_,
        v_fvarId_2511_,
        v_a_2512_,
        v_a_2513_,
    );
    lean_dec(v_a_2513_);
    lean_dec(v_a_2512_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceLet(
    mut v_decl_2516_: *mut LeanObject,
    mut v_fvarId_2517_: *mut LeanObject,
    mut v_a_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v_a_2520_: *mut LeanObject,
    mut v_a_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(
        v_decl_2516_,
        v_fvarId_2517_,
        v_a_2518_,
        v_a_2520_,
    );
    return v___x_2524_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(
    mut v_decl_2525_: *mut LeanObject,
    mut v_fvarId_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
    mut v_a_2529_: *mut LeanObject,
    mut v_a_2530_: *mut LeanObject,
    mut v_a_2531_: *mut LeanObject,
    mut v_a_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2533_: *mut LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Lean_Compiler_LCNF_CSE_replaceLet(
        v_decl_2525_,
        v_fvarId_2526_,
        v_a_2527_,
        v_a_2528_,
        v_a_2529_,
        v_a_2530_,
        v_a_2531_,
    );
    lean_dec(v_a_2531_);
    lean_dec_ref(v_a_2530_);
    lean_dec(v_a_2529_);
    lean_dec_ref(v_a_2528_);
    lean_dec(v_a_2527_);
    return v_res_2533_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0(
    mut v_00_u03b2_2534_: *mut LeanObject,
    mut v_m_2535_: *mut LeanObject,
    mut v_a_2536_: *mut LeanObject,
    mut v_b_2537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    v___x_2538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_m_2535_, v_a_2536_, v_b_2537_);
    return v___x_2538_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(
    mut v_00_u03b2_2539_: *mut LeanObject,
    mut v_a_2540_: *mut LeanObject,
    mut v_x_2541_: *mut LeanObject,
) -> u8 {
    let mut v___x_2542_: u8 = 0;
    v___x_2542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___redArg(v_a_2540_, v_x_2541_);
    return v___x_2542_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0___boxed(
    mut v_00_u03b2_2543_: *mut LeanObject,
    mut v_a_2544_: *mut LeanObject,
    mut v_x_2545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2546_: u8 = 0;
    let mut v_r_2547_: *mut LeanObject = core::ptr::null_mut();
    v_res_2546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__0(v_00_u03b2_2543_, v_a_2544_, v_x_2545_);
    lean_dec(v_x_2545_);
    lean_dec(v_a_2544_);
    v_r_2547_ = lean_box((v_res_2546_) as usize);
    return v_r_2547_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1(
    mut v_00_u03b2_2548_: *mut LeanObject,
    mut v_data_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    v___x_2550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1___redArg(v_data_2549_);
    return v___x_2550_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2(
    mut v_00_u03b2_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
    mut v_b_2553_: *mut LeanObject,
    mut v_x_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    v___x_2555_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__2___redArg(v_a_2552_, v_b_2553_, v_x_2554_);
    return v___x_2555_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2556_: *mut LeanObject,
    mut v_i_2557_: *mut LeanObject,
    mut v_source_2558_: *mut LeanObject,
    mut v_target_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    v___x_2560_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2___redArg(v_i_2557_, v_source_2558_, v_target_2559_);
    return v___x_2560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2561_: *mut LeanObject,
    mut v_x_2562_: *mut LeanObject,
    mut v_x_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    v___x_2564_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2562_, v_x_2563_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(
    mut v_decl_2565_: *mut LeanObject,
    mut v_fvarId_2566_: *mut LeanObject,
    mut v_a_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2570_: u8 = 0;
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v_fvarId_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2582_: u8 = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2593_: u8 = 0;
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut v_unused_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2570_ = 0;
                v___x_2571_ = 1;
                v___x_2572_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                    v___x_2570_,
                    v_decl_2565_,
                    v___x_2571_,
                    v_a_2568_,
                );
                if lean_obj_tag(v___x_2572_) == 0 {
                    v_isSharedCheck_2594_ = (!lean_is_exclusive(v___x_2572_)) as u8;
                    if v_isSharedCheck_2594_ == 0 {
                        v_unused_2595_ = lean_ctor_get(v___x_2572_, 0);
                        lean_dec(v_unused_2595_);
                        v___x_2574_ = v___x_2572_;
                        v_isShared_2575_ = v_isSharedCheck_2594_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2572_);
                        v___x_2574_ = lean_box(0);
                        v_isShared_2575_ = v_isSharedCheck_2594_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fvarId_2566_);
                    lean_dec_ref(v_decl_2565_);
                    return v___x_2572_;
                }
            }
            1 => {
                v_fvarId_2576_ = lean_ctor_get(v_decl_2565_, 0);
                lean_inc(v_fvarId_2576_);
                lean_dec_ref(v_decl_2565_);
                v___x_2577_ = lean_st_ref_take(v_a_2567_);
                v_map_2578_ = lean_ctor_get(v___x_2577_, 0);
                v_subst_2579_ = lean_ctor_get(v___x_2577_, 1);
                v_isSharedCheck_2593_ = (!lean_is_exclusive(v___x_2577_)) as u8;
                if v_isSharedCheck_2593_ == 0 {
                    v___x_2581_ = v___x_2577_;
                    v_isShared_2582_ = v_isSharedCheck_2593_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_subst_2579_);
                    lean_inc(v_map_2578_);
                    lean_dec(v___x_2577_);
                    v___x_2581_ = lean_box(0);
                    v_isShared_2582_ = v_isSharedCheck_2593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2583_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2583_, 0, v_fvarId_2566_);
                v___x_2584_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_CSE_replaceLet_spec__0___redArg(v_subst_2579_, v_fvarId_2576_, v___x_2583_);
                if v_isShared_2582_ == 0 {
                    lean_ctor_set(v___x_2581_, 1, v___x_2584_);
                    v___x_2586_ = v___x_2581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_map_2578_);
                    lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___x_2584_);
                    v___x_2586_ = v_reuseFailAlloc_2592_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2587_ = lean_st_ref_set(v_a_2567_, v___x_2586_);
                v___x_2588_ = lean_box(0);
                if v_isShared_2575_ == 0 {
                    lean_ctor_set(v___x_2574_, 0, v___x_2588_);
                    v___x_2590_ = v___x_2574_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
                    v___x_2590_ = v_reuseFailAlloc_2591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceFun___redArg___boxed(
    mut v_decl_2596_: *mut LeanObject,
    mut v_fvarId_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2601_: *mut LeanObject = core::ptr::null_mut();
    v_res_2601_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(
        v_decl_2596_,
        v_fvarId_2597_,
        v_a_2598_,
        v_a_2599_,
    );
    lean_dec(v_a_2599_);
    lean_dec(v_a_2598_);
    return v_res_2601_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceFun(
    mut v_decl_2602_: *mut LeanObject,
    mut v_fvarId_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    v___x_2610_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(
        v_decl_2602_,
        v_fvarId_2603_,
        v_a_2604_,
        v_a_2606_,
    );
    return v___x_2610_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(
    mut v_decl_2611_: *mut LeanObject,
    mut v_fvarId_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
    mut v_a_2615_: *mut LeanObject,
    mut v_a_2616_: *mut LeanObject,
    mut v_a_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2619_: *mut LeanObject = core::ptr::null_mut();
    v_res_2619_ = l_Lean_Compiler_LCNF_CSE_replaceFun(
        v_decl_2611_,
        v_fvarId_2612_,
        v_a_2613_,
        v_a_2614_,
        v_a_2615_,
        v_a_2616_,
        v_a_2617_,
    );
    lean_dec(v_a_2617_);
    lean_dec_ref(v_a_2616_);
    lean_dec(v_a_2615_);
    lean_dec_ref(v_a_2614_);
    lean_dec(v_a_2613_);
    return v_res_2619_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(
    mut v_v_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut v_unused_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: u8 = 0;
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_v_2620_) {
                0 => {
                    v_isSharedCheck_2631_ = (!lean_is_exclusive(v_v_2620_)) as u8;
                    if v_isSharedCheck_2631_ == 0 {
                        v_unused_2632_ = lean_ctor_get(v_v_2620_, 0);
                        lean_dec(v_unused_2632_);
                        v___x_2624_ = v_v_2620_;
                        v_isShared_2625_ = v_isSharedCheck_2631_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_2620_);
                        v___x_2624_ = lean_box(0);
                        v_isShared_2625_ = v_isSharedCheck_2631_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_declName_2633_ = lean_ctor_get(v_v_2620_, 0);
                    lean_inc(v_declName_2633_);
                    lean_dec_ref_known(v_v_2620_, 3);
                    v___x_2634_ = lean_st_ref_get(v_a_2621_);
                    v_env_2635_ = lean_ctor_get(v___x_2634_, 0);
                    lean_inc_ref(v_env_2635_);
                    lean_dec(v___x_2634_);
                    v___x_2636_ = l_Lean_hasNeverExtractAttribute(v_env_2635_, v_declName_2633_);
                    v___x_2637_ = lean_box((v___x_2636_) as usize);
                    v___x_2638_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2638_, 0, v___x_2637_);
                    return v___x_2638_;
                }
                _ => {
                    lean_dec(v_v_2620_);
                    v___x_2639_ = 0;
                    v___x_2640_ = lean_box((v___x_2639_) as usize);
                    v___x_2641_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2641_, 0, v___x_2640_);
                    return v___x_2641_;
                }
            },
            1 => {
                v___x_2626_ = 0;
                v___x_2627_ = lean_box((v___x_2626_) as usize);
                if v_isShared_2625_ == 0 {
                    lean_ctor_set(v___x_2624_, 0, v___x_2627_);
                    v___x_2629_ = v___x_2624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
                    v___x_2629_ = v_reuseFailAlloc_2630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg___boxed(
    mut v_v_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2645_: *mut LeanObject = core::ptr::null_mut();
    v_res_2645_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_2642_, v_a_2643_);
    lean_dec(v_a_2643_);
    return v_res_2645_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_hasNeverExtract(
    mut v_v_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(v_v_2646_, v_a_2650_);
    return v___x_2652_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CSE_hasNeverExtract___boxed(
    mut v_v_2653_: *mut LeanObject,
    mut v_a_2654_: *mut LeanObject,
    mut v_a_2655_: *mut LeanObject,
    mut v_a_2656_: *mut LeanObject,
    mut v_a_2657_: *mut LeanObject,
    mut v_a_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2659_: *mut LeanObject = core::ptr::null_mut();
    v_res_2659_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract(
        v_v_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_,
    );
    lean_dec(v_a_2657_);
    lean_dec_ref(v_a_2656_);
    lean_dec(v_a_2655_);
    lean_dec_ref(v_a_2654_);
    return v_res_2659_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(
    mut v_a_2660_: *mut LeanObject,
    mut v_map_2661_: *mut LeanObject,
    mut v_a_x3f_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2675_: u8 = 0;
    let mut v_unused_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2664_ = lean_st_ref_take(v_a_2660_);
                v_subst_2665_ = lean_ctor_get(v___x_2664_, 1);
                v_isSharedCheck_2675_ = (!lean_is_exclusive(v___x_2664_)) as u8;
                if v_isSharedCheck_2675_ == 0 {
                    v_unused_2676_ = lean_ctor_get(v___x_2664_, 0);
                    lean_dec(v_unused_2676_);
                    v___x_2667_ = v___x_2664_;
                    v_isShared_2668_ = v_isSharedCheck_2675_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_subst_2665_);
                    lean_dec(v___x_2664_);
                    v___x_2667_ = lean_box(0);
                    v_isShared_2668_ = v_isSharedCheck_2675_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2668_ == 0 {
                    lean_ctor_set(v___x_2667_, 0, v_map_2661_);
                    v___x_2670_ = v___x_2667_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_map_2661_);
                    lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_subst_2665_);
                    v___x_2670_ = v_reuseFailAlloc_2674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2671_ = lean_st_ref_set(v_a_2660_, v___x_2670_);
                v___x_2672_ = lean_box(0);
                v___x_2673_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2673_, 0, v___x_2672_);
                return v___x_2673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0___boxed(
    mut v_a_2677_: *mut LeanObject,
    mut v_map_2678_: *mut LeanObject,
    mut v_a_x3f_2679_: *mut LeanObject,
    mut v___y_2680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2681_: *mut LeanObject = core::ptr::null_mut();
    v_res_2681_ =
        l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(
            v_a_2677_,
            v_map_2678_,
            v_a_x3f_2679_,
        );
    lean_dec(v_a_x3f_2679_);
    lean_dec(v_a_2677_);
    return v_res_2681_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(
    mut v_pu_2682_: u8,
    mut v_t_2683_: u8,
    mut v_args_2684_: *mut LeanObject,
    mut v___y_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    v___x_2687_ = lean_st_ref_get(v___y_2685_);
    v_subst_2688_ = lean_ctor_get(v___x_2687_, 1);
    lean_inc_ref(v_subst_2688_);
    lean_dec(v___x_2687_);
    v___x_2689_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_2682_,
        v_subst_2688_,
        v_args_2684_,
        v_t_2683_,
    );
    lean_dec_ref(v_subst_2688_);
    v___x_2690_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2690_, 0, v___x_2689_);
    return v___x_2690_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg___boxed(
    mut v_pu_2691_: *mut LeanObject,
    mut v_t_2692_: *mut LeanObject,
    mut v_args_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2696_: u8 = 0;
    let mut v_t_boxed_2697_: u8 = 0;
    let mut v_res_2698_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2696_ = (lean_unbox(v_pu_2691_) as u8);
    v_t_boxed_2697_ = (lean_unbox(v_t_2692_) as u8);
    v_res_2698_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_boxed_2696_, v_t_boxed_2697_, v_args_2693_, v___y_2694_);
    lean_dec(v___y_2694_);
    return v_res_2698_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(
    mut v_pu_2699_: u8,
    mut v_t_2700_: u8,
    mut v_decl_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    v_type_2705_ = lean_ctor_get(v_decl_2701_, 2);
    v_value_2706_ = lean_ctor_get(v_decl_2701_, 3);
    v___x_2707_ = lean_st_ref_get(v___y_2702_);
    v_subst_2708_ = lean_ctor_get(v___x_2707_, 1);
    lean_inc_ref(v_subst_2708_);
    lean_dec(v___x_2707_);
    v___x_2709_ = lean_st_ref_get(v___y_2702_);
    v_subst_2710_ = lean_ctor_get(v___x_2709_, 1);
    lean_inc_ref(v_subst_2710_);
    lean_dec(v___x_2709_);
    lean_inc_ref(v_type_2705_);
    v___x_2711_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_2699_,
        v_subst_2708_,
        v_t_2700_,
        v_type_2705_,
    );
    lean_dec_ref(v_subst_2708_);
    lean_inc(v_value_2706_);
    v___x_2712_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_2699_,
        v_subst_2710_,
        v_value_2706_,
        v_t_2700_,
    );
    lean_dec_ref(v_subst_2710_);
    v___x_2713_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
            v_pu_2699_,
            v_decl_2701_,
            v___x_2711_,
            v___x_2712_,
            v___y_2703_,
        );
    return v___x_2713_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg___boxed(
    mut v_pu_2714_: *mut LeanObject,
    mut v_t_2715_: *mut LeanObject,
    mut v_decl_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2720_: u8 = 0;
    let mut v_t_boxed_2721_: u8 = 0;
    let mut v_res_2722_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2720_ = (lean_unbox(v_pu_2714_) as u8);
    v_t_boxed_2721_ = (lean_unbox(v_t_2715_) as u8);
    v_res_2722_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_boxed_2720_, v_t_boxed_2721_, v_decl_2716_, v___y_2717_, v___y_2718_);
    lean_dec(v___y_2718_);
    lean_dec(v___y_2717_);
    return v_res_2722_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(
    mut v___y_2723_: *mut LeanObject,
    mut v_map_2724_: *mut LeanObject,
    mut v_a_x3f_2725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2731_: u8 = 0;
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_unused_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2727_ = lean_st_ref_take(v___y_2723_);
                v_subst_2728_ = lean_ctor_get(v___x_2727_, 1);
                v_isSharedCheck_2738_ = (!lean_is_exclusive(v___x_2727_)) as u8;
                if v_isSharedCheck_2738_ == 0 {
                    v_unused_2739_ = lean_ctor_get(v___x_2727_, 0);
                    lean_dec(v_unused_2739_);
                    v___x_2730_ = v___x_2727_;
                    v_isShared_2731_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_subst_2728_);
                    lean_dec(v___x_2727_);
                    v___x_2730_ = lean_box(0);
                    v_isShared_2731_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2731_ == 0 {
                    lean_ctor_set(v___x_2730_, 0, v_map_2724_);
                    v___x_2733_ = v___x_2730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_map_2724_);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_subst_2728_);
                    v___x_2733_ = v_reuseFailAlloc_2737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2734_ = lean_st_ref_set(v___y_2723_, v___x_2733_);
                v___x_2735_ = lean_box(0);
                v___x_2736_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2736_, 0, v___x_2735_);
                return v___x_2736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0___boxed(
    mut v___y_2740_: *mut LeanObject,
    mut v_map_2741_: *mut LeanObject,
    mut v_a_x3f_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2744_: *mut LeanObject = core::ptr::null_mut();
    v_res_2744_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_2740_, v_map_2741_, v_a_x3f_2742_);
    lean_dec(v_a_x3f_2742_);
    lean_dec(v___y_2740_);
    return v_res_2744_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(
    mut v_pu_2745_: u8,
    mut v_t_2746_: u8,
    mut v_i_2747_: *mut LeanObject,
    mut v_as_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: usize = 0;
    let mut v___x_2763_: usize = 0;
    let mut v___x_2764_: u8 = 0;
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2752_ = lean_array_get_size(v_as_2748_);
                v___x_2753_ = lean_nat_dec_lt(v_i_2747_, v___x_2752_);
                if v___x_2753_ == 0 {
                    lean_dec(v_i_2747_);
                    v___x_2754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2754_, 0, v_as_2748_);
                    return v___x_2754_;
                } else {
                    v_a_2755_ = lean_array_fget_borrowed(v_as_2748_, v_i_2747_);
                    v_type_2756_ = lean_ctor_get(v_a_2755_, 2);
                    v___x_2757_ = lean_st_ref_get(v___y_2749_);
                    v_subst_2758_ = lean_ctor_get(v___x_2757_, 1);
                    lean_inc_ref(v_subst_2758_);
                    lean_dec(v___x_2757_);
                    lean_inc_ref(v_type_2756_);
                    v___x_2759_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_2745_, v_subst_2758_, v_t_2746_, v_type_2756_);
                    lean_dec_ref(v_subst_2758_);
                    lean_inc(v_a_2755_);
                    v___x_2760_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_2745_, v_a_2755_, v___x_2759_, v___y_2750_);
                    if lean_obj_tag(v___x_2760_) == 0 {
                        v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
                        lean_inc(v_a_2761_);
                        lean_dec_ref_known(v___x_2760_, 1);
                        v___x_2762_ = lean_ptr_addr(v_a_2755_);
                        v___x_2763_ = lean_ptr_addr(v_a_2761_);
                        v___x_2764_ = lean_usize_dec_eq(v___x_2762_, v___x_2763_);
                        if v___x_2764_ == 0 {
                            v___x_2765_ = lean_unsigned_to_nat(1);
                            v___x_2766_ = lean_nat_add(v_i_2747_, v___x_2765_);
                            v___x_2767_ = lean_array_fset(v_as_2748_, v_i_2747_, v_a_2761_);
                            lean_dec(v_i_2747_);
                            v_i_2747_ = v___x_2766_;
                            v_as_2748_ = v___x_2767_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_2761_);
                            v___x_2769_ = lean_unsigned_to_nat(1);
                            v___x_2770_ = lean_nat_add(v_i_2747_, v___x_2769_);
                            lean_dec(v_i_2747_);
                            v_i_2747_ = v___x_2770_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_2748_);
                        lean_dec(v_i_2747_);
                        v_a_2772_ = lean_ctor_get(v___x_2760_, 0);
                        v_isSharedCheck_2779_ = (!lean_is_exclusive(v___x_2760_)) as u8;
                        if v_isSharedCheck_2779_ == 0 {
                            v___x_2774_ = v___x_2760_;
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2772_);
                            lean_dec(v___x_2760_);
                            v___x_2774_ = lean_box(0);
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2775_ == 0 {
                    v___x_2777_ = v___x_2774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg___boxed(
    mut v_pu_2780_: *mut LeanObject,
    mut v_t_2781_: *mut LeanObject,
    mut v_i_2782_: *mut LeanObject,
    mut v_as_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2787_: u8 = 0;
    let mut v_t_boxed_2788_: u8 = 0;
    let mut v_res_2789_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2787_ = (lean_unbox(v_pu_2780_) as u8);
    v_t_boxed_2788_ = (lean_unbox(v_t_2781_) as u8);
    v_res_2789_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_boxed_2787_, v_t_boxed_2788_, v_i_2782_, v_as_2783_, v___y_2784_, v___y_2785_);
    lean_dec(v___y_2785_);
    lean_dec(v___y_2784_);
    return v_res_2789_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(
    mut v_pu_2790_: u8,
    mut v_t_2791_: u8,
    mut v_ps_2792_: *mut LeanObject,
    mut v___y_2793_: *mut LeanObject,
    mut v___y_2794_: *mut LeanObject,
    mut v___y_2795_: *mut LeanObject,
    mut v___y_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    v___x_2799_ = lean_unsigned_to_nat(0);
    v___x_2800_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_2790_, v_t_2791_, v___x_2799_, v_ps_2792_, v___y_2793_, v___y_2795_);
    return v___x_2800_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0___boxed(
    mut v_pu_2801_: *mut LeanObject,
    mut v_t_2802_: *mut LeanObject,
    mut v_ps_2803_: *mut LeanObject,
    mut v___y_2804_: *mut LeanObject,
    mut v___y_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
    mut v___y_2808_: *mut LeanObject,
    mut v___y_2809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2810_: u8 = 0;
    let mut v_t_boxed_2811_: u8 = 0;
    let mut v_res_2812_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2810_ = (lean_unbox(v_pu_2801_) as u8);
    v_t_boxed_2811_ = (lean_unbox(v_t_2802_) as u8);
    v_res_2812_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v_pu_boxed_2810_, v_t_boxed_2811_, v_ps_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
    lean_dec(v___y_2808_);
    lean_dec_ref(v___y_2807_);
    lean_dec(v___y_2806_);
    lean_dec_ref(v___y_2805_);
    lean_dec(v___y_2804_);
    return v_res_2812_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(
    mut v_keys_2813_: *mut LeanObject,
    mut v_vals_2814_: *mut LeanObject,
    mut v_i_2815_: *mut LeanObject,
    mut v_k_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2817_ = lean_array_get_size(v_keys_2813_);
                v___x_2818_ = lean_nat_dec_lt(v_i_2815_, v___x_2817_);
                if v___x_2818_ == 0 {
                    lean_dec(v_i_2815_);
                    v___x_2819_ = lean_box(0);
                    return v___x_2819_;
                } else {
                    v_k_x27_2820_ = lean_array_fget_borrowed(v_keys_2813_, v_i_2815_);
                    v___x_2821_ = lean_expr_eqv(v_k_2816_, v_k_x27_2820_);
                    if v___x_2821_ == 0 {
                        v___x_2822_ = lean_unsigned_to_nat(1);
                        v___x_2823_ = lean_nat_add(v_i_2815_, v___x_2822_);
                        lean_dec(v_i_2815_);
                        v_i_2815_ = v___x_2823_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2825_ = lean_array_fget_borrowed(v_vals_2814_, v_i_2815_);
                        lean_dec(v_i_2815_);
                        lean_inc(v___x_2825_);
                        v___x_2826_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2826_, 0, v___x_2825_);
                        return v___x_2826_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_keys_2827_: *mut LeanObject,
    mut v_vals_2828_: *mut LeanObject,
    mut v_i_2829_: *mut LeanObject,
    mut v_k_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2831_: *mut LeanObject = core::ptr::null_mut();
    v_res_2831_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_2827_, v_vals_2828_, v_i_2829_, v_k_2830_);
    lean_dec_ref(v_k_2830_);
    lean_dec_ref(v_vals_2828_);
    lean_dec_ref(v_keys_2827_);
    return v_res_2831_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_2832_: usize = 0;
    let mut v___x_2833_: usize = 0;
    let mut v___x_2834_: usize = 0;
    v___x_2832_ = 5usize;
    v___x_2833_ = 1usize;
    v___x_2834_ = lean_usize_shift_left(v___x_2833_, v___x_2832_);
    return v___x_2834_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_2835_: usize = 0;
    let mut v___x_2836_: usize = 0;
    let mut v___x_2837_: usize = 0;
    v___x_2835_ = 1usize;
    v___x_2836_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__0);
    v___x_2837_ = lean_usize_sub(v___x_2836_, v___x_2835_);
    return v___x_2837_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(
    mut v_x_2838_: *mut LeanObject,
    mut v_x_2839_: usize,
    mut v_x_2840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: usize = 0;
    let mut v___x_2844_: usize = 0;
    let mut v___x_2845_: usize = 0;
    let mut v_j_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: u8 = 0;
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: usize = 0;
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2838_) == 0 {
                    v_es_2841_ = lean_ctor_get(v_x_2838_, 0);
                    v___x_2842_ = lean_box(2);
                    v___x_2843_ = 5usize;
                    v___x_2844_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1);
                    v___x_2845_ = lean_usize_land(v_x_2839_, v___x_2844_);
                    v_j_2846_ = lean_usize_to_nat(v___x_2845_);
                    v___x_2847_ = lean_array_get_borrowed(v___x_2842_, v_es_2841_, v_j_2846_);
                    lean_dec(v_j_2846_);
                    match lean_obj_tag(v___x_2847_) {
                        0 => {
                            v_key_2848_ = lean_ctor_get(v___x_2847_, 0);
                            v_val_2849_ = lean_ctor_get(v___x_2847_, 1);
                            v___x_2850_ = lean_expr_eqv(v_x_2840_, v_key_2848_);
                            if v___x_2850_ == 0 {
                                v___x_2851_ = lean_box(0);
                                return v___x_2851_;
                            } else {
                                lean_inc(v_val_2849_);
                                v___x_2852_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2852_, 0, v_val_2849_);
                                return v___x_2852_;
                            }
                        }
                        1 => {
                            v_node_2853_ = lean_ctor_get(v___x_2847_, 0);
                            v___x_2854_ = lean_usize_shift_right(v_x_2839_, v___x_2843_);
                            v_x_2838_ = v_node_2853_;
                            v_x_2839_ = v___x_2854_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2856_ = lean_box(0);
                            return v___x_2856_;
                        }
                    }
                } else {
                    v_ks_2857_ = lean_ctor_get(v_x_2838_, 0);
                    v_vs_2858_ = lean_ctor_get(v_x_2838_, 1);
                    v___x_2859_ = lean_unsigned_to_nat(0);
                    v___x_2860_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_ks_2857_, v_vs_2858_, v___x_2859_, v_x_2840_);
                    return v___x_2860_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___boxed(
    mut v_x_2861_: *mut LeanObject,
    mut v_x_2862_: *mut LeanObject,
    mut v_x_2863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_15785__boxed_2864_: usize = 0;
    let mut v_res_2865_: *mut LeanObject = core::ptr::null_mut();
    v_x_15785__boxed_2864_ = lean_unbox_usize(v_x_2862_);
    lean_dec(v_x_2862_);
    v_res_2865_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_2861_, v_x_15785__boxed_2864_, v_x_2863_);
    lean_dec_ref(v_x_2863_);
    lean_dec_ref(v_x_2861_);
    return v_res_2865_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(
    mut v_x_2866_: *mut LeanObject,
    mut v_x_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2868_: u64 = 0;
    let mut v___x_2869_: usize = 0;
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    v___x_2868_ = l_Lean_Expr_hash(v_x_2867_);
    v___x_2869_ = lean_uint64_to_usize(v___x_2868_);
    v___x_2870_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_2866_, v___x_2869_, v_x_2867_);
    return v___x_2870_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg___boxed(
    mut v_x_2871_: *mut LeanObject,
    mut v_x_2872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2873_: *mut LeanObject = core::ptr::null_mut();
    v_res_2873_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_2871_, v_x_2872_);
    lean_dec_ref(v_x_2872_);
    lean_dec_ref(v_x_2871_);
    return v_res_2873_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(
    mut v_x_2874_: *mut LeanObject,
    mut v_x_2875_: *mut LeanObject,
    mut v_x_2876_: *mut LeanObject,
    mut v_x_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2878_ = lean_ctor_get(v_x_2874_, 0);
                v_vs_2879_ = lean_ctor_get(v_x_2874_, 1);
                v_isSharedCheck_2903_ = (!lean_is_exclusive(v_x_2874_)) as u8;
                if v_isSharedCheck_2903_ == 0 {
                    v___x_2881_ = v_x_2874_;
                    v_isShared_2882_ = v_isSharedCheck_2903_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2879_);
                    lean_inc(v_ks_2878_);
                    lean_dec(v_x_2874_);
                    v___x_2881_ = lean_box(0);
                    v_isShared_2882_ = v_isSharedCheck_2903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2883_ = lean_array_get_size(v_ks_2878_);
                v___x_2884_ = lean_nat_dec_lt(v_x_2875_, v___x_2883_);
                if v___x_2884_ == 0 {
                    lean_dec(v_x_2875_);
                    v___x_2885_ = lean_array_push(v_ks_2878_, v_x_2876_);
                    v___x_2886_ = lean_array_push(v_vs_2879_, v_x_2877_);
                    if v_isShared_2882_ == 0 {
                        lean_ctor_set(v___x_2881_, 1, v___x_2886_);
                        lean_ctor_set(v___x_2881_, 0, v___x_2885_);
                        v___x_2888_ = v___x_2881_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2885_);
                        lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2886_);
                        v___x_2888_ = v_reuseFailAlloc_2889_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2890_ = lean_array_fget_borrowed(v_ks_2878_, v_x_2875_);
                    v___x_2891_ = lean_expr_eqv(v_x_2876_, v_k_x27_2890_);
                    if v___x_2891_ == 0 {
                        if v_isShared_2882_ == 0 {
                            v___x_2893_ = v___x_2881_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_ks_2878_);
                            lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_vs_2879_);
                            v___x_2893_ = v_reuseFailAlloc_2897_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2898_ = lean_array_fset(v_ks_2878_, v_x_2875_, v_x_2876_);
                        v___x_2899_ = lean_array_fset(v_vs_2879_, v_x_2875_, v_x_2877_);
                        lean_dec(v_x_2875_);
                        if v_isShared_2882_ == 0 {
                            lean_ctor_set(v___x_2881_, 1, v___x_2899_);
                            lean_ctor_set(v___x_2881_, 0, v___x_2898_);
                            v___x_2901_ = v___x_2881_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2898_);
                            lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2899_);
                            v___x_2901_ = v_reuseFailAlloc_2902_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2888_;
            }
            3 => {
                v___x_2894_ = lean_unsigned_to_nat(1);
                v___x_2895_ = lean_nat_add(v_x_2875_, v___x_2894_);
                lean_dec(v_x_2875_);
                v_x_2874_ = v___x_2893_;
                v_x_2875_ = v___x_2895_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(
    mut v_n_2904_: *mut LeanObject,
    mut v_k_2905_: *mut LeanObject,
    mut v_v_2906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    v___x_2907_ = lean_unsigned_to_nat(0);
    v___x_2908_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_n_2904_, v___x_2907_, v_k_2905_, v_v_2906_);
    return v___x_2908_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v___x_2909_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2909_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(
    mut v_x_2910_: *mut LeanObject,
    mut v_x_2911_: usize,
    mut v_x_2912_: usize,
    mut v_x_2913_: *mut LeanObject,
    mut v_x_2914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: usize = 0;
    let mut v___x_2917_: usize = 0;
    let mut v___x_2918_: usize = 0;
    let mut v___x_2919_: usize = 0;
    let mut v_j_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2925_: u8 = 0;
    let mut v_v_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2946_: u8 = 0;
    let mut v_node_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2951_: usize = 0;
    let mut v___x_2952_: usize = 0;
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2957_: u8 = 0;
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_unused_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2965_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: u8 = 0;
    let mut v_ks_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: usize = 0;
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v_reuseFailAlloc_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2910_) == 0 {
                    v_es_2915_ = lean_ctor_get(v_x_2910_, 0);
                    v___x_2916_ = 5usize;
                    v___x_2917_ = 1usize;
                    v___x_2918_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg___closed__1);
                    v___x_2919_ = lean_usize_land(v_x_2911_, v___x_2918_);
                    v_j_2920_ = lean_usize_to_nat(v___x_2919_);
                    v___x_2921_ = lean_array_get_size(v_es_2915_);
                    v___x_2922_ = lean_nat_dec_lt(v_j_2920_, v___x_2921_);
                    if v___x_2922_ == 0 {
                        lean_dec(v_j_2920_);
                        lean_dec(v_x_2914_);
                        lean_dec_ref(v_x_2913_);
                        return v_x_2910_;
                    } else {
                        lean_inc_ref(v_es_2915_);
                        v_isSharedCheck_2959_ = (!lean_is_exclusive(v_x_2910_)) as u8;
                        if v_isSharedCheck_2959_ == 0 {
                            v_unused_2960_ = lean_ctor_get(v_x_2910_, 0);
                            lean_dec(v_unused_2960_);
                            v___x_2924_ = v_x_2910_;
                            v_isShared_2925_ = v_isSharedCheck_2959_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2910_);
                            v___x_2924_ = lean_box(0);
                            v_isShared_2925_ = v_isSharedCheck_2959_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2961_ = lean_ctor_get(v_x_2910_, 0);
                    v_vs_2962_ = lean_ctor_get(v_x_2910_, 1);
                    v_isSharedCheck_2982_ = (!lean_is_exclusive(v_x_2910_)) as u8;
                    if v_isSharedCheck_2982_ == 0 {
                        v___x_2964_ = v_x_2910_;
                        v_isShared_2965_ = v_isSharedCheck_2982_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2962_);
                        lean_inc(v_ks_2961_);
                        lean_dec(v_x_2910_);
                        v___x_2964_ = lean_box(0);
                        v_isShared_2965_ = v_isSharedCheck_2982_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2926_ = lean_array_fget(v_es_2915_, v_j_2920_);
                v___x_2927_ = lean_box(0);
                v_xs_x27_2928_ = lean_array_fset(v_es_2915_, v_j_2920_, v___x_2927_);
                match lean_obj_tag(v_v_2926_) {
                    0 => {
                        v_key_2935_ = lean_ctor_get(v_v_2926_, 0);
                        v_val_2936_ = lean_ctor_get(v_v_2926_, 1);
                        v_isSharedCheck_2946_ = (!lean_is_exclusive(v_v_2926_)) as u8;
                        if v_isSharedCheck_2946_ == 0 {
                            v___x_2938_ = v_v_2926_;
                            v_isShared_2939_ = v_isSharedCheck_2946_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2936_);
                            lean_inc(v_key_2935_);
                            lean_dec(v_v_2926_);
                            v___x_2938_ = lean_box(0);
                            v_isShared_2939_ = v_isSharedCheck_2946_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2947_ = lean_ctor_get(v_v_2926_, 0);
                        v_isSharedCheck_2957_ = (!lean_is_exclusive(v_v_2926_)) as u8;
                        if v_isSharedCheck_2957_ == 0 {
                            v___x_2949_ = v_v_2926_;
                            v_isShared_2950_ = v_isSharedCheck_2957_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2947_);
                            lean_dec(v_v_2926_);
                            v___x_2949_ = lean_box(0);
                            v_isShared_2950_ = v_isSharedCheck_2957_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2958_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2958_, 0, v_x_2913_);
                        lean_ctor_set(v___x_2958_, 1, v_x_2914_);
                        v___y_2930_ = v___x_2958_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2931_ = lean_array_fset(v_xs_x27_2928_, v_j_2920_, v___y_2930_);
                lean_dec(v_j_2920_);
                if v_isShared_2925_ == 0 {
                    lean_ctor_set(v___x_2924_, 0, v___x_2931_);
                    v___x_2933_ = v___x_2924_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2933_;
            }
            4 => {
                v___x_2940_ = lean_expr_eqv(v_x_2913_, v_key_2935_);
                if v___x_2940_ == 0 {
                    lean_del_object(v___x_2938_);
                    v___x_2941_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2935_,
                        v_val_2936_,
                        v_x_2913_,
                        v_x_2914_,
                    );
                    v___x_2942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2942_, 0, v___x_2941_);
                    v___y_2930_ = v___x_2942_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2936_);
                    lean_dec(v_key_2935_);
                    if v_isShared_2939_ == 0 {
                        lean_ctor_set(v___x_2938_, 1, v_x_2914_);
                        lean_ctor_set(v___x_2938_, 0, v_x_2913_);
                        v___x_2944_ = v___x_2938_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_x_2913_);
                        lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_x_2914_);
                        v___x_2944_ = v_reuseFailAlloc_2945_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2930_ = v___x_2944_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2951_ = lean_usize_shift_right(v_x_2911_, v___x_2916_);
                v___x_2952_ = lean_usize_add(v_x_2912_, v___x_2917_);
                v___x_2953_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_node_2947_, v___x_2951_, v___x_2952_, v_x_2913_, v_x_2914_);
                if v_isShared_2950_ == 0 {
                    lean_ctor_set(v___x_2949_, 0, v___x_2953_);
                    v___x_2955_ = v___x_2949_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
                    v___x_2955_ = v_reuseFailAlloc_2956_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2930_ = v___x_2955_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2965_ == 0 {
                    v___x_2967_ = v___x_2964_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_ks_2961_);
                    lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_vs_2962_);
                    v___x_2967_ = v_reuseFailAlloc_2981_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2968_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v___x_2967_, v_x_2913_, v_x_2914_);
                v___x_2976_ = 7usize;
                v___x_2977_ = lean_usize_dec_le(v___x_2976_, v_x_2912_);
                if v___x_2977_ == 0 {
                    v___x_2978_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2968_);
                    v___x_2979_ = lean_unsigned_to_nat(4);
                    v___x_2980_ = lean_nat_dec_lt(v___x_2978_, v___x_2979_);
                    lean_dec(v___x_2978_);
                    v___y_2970_ = v___x_2980_;
                    state = 10;
                    continue;
                } else {
                    v___y_2970_ = v___x_2977_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2970_ == 0 {
                    v_ks_2971_ = lean_ctor_get(v_newNode_2968_, 0);
                    lean_inc_ref(v_ks_2971_);
                    v_vs_2972_ = lean_ctor_get(v_newNode_2968_, 1);
                    lean_inc_ref(v_vs_2972_);
                    lean_dec_ref(v_newNode_2968_);
                    v___x_2973_ = lean_unsigned_to_nat(0);
                    v___x_2974_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___closed__0);
                    v___x_2975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_x_2912_, v_ks_2971_, v_vs_2972_, v___x_2973_, v___x_2974_);
                    lean_dec_ref(v_vs_2972_);
                    lean_dec_ref(v_ks_2971_);
                    return v___x_2975_;
                } else {
                    return v_newNode_2968_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(
    mut v_depth_2983_: usize,
    mut v_keys_2984_: *mut LeanObject,
    mut v_vals_2985_: *mut LeanObject,
    mut v_i_2986_: *mut LeanObject,
    mut v_entries_2987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: u8 = 0;
    let mut v_k_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: u64 = 0;
    let mut v_h_2993_: usize = 0;
    let mut v___x_2994_: usize = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: usize = 0;
    let mut v___x_2997_: usize = 0;
    let mut v___x_2998_: usize = 0;
    let mut v_h_2999_: usize = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2988_ = lean_array_get_size(v_keys_2984_);
                v___x_2989_ = lean_nat_dec_lt(v_i_2986_, v___x_2988_);
                if v___x_2989_ == 0 {
                    lean_dec(v_i_2986_);
                    return v_entries_2987_;
                } else {
                    v_k_2990_ = lean_array_fget_borrowed(v_keys_2984_, v_i_2986_);
                    v_v_2991_ = lean_array_fget_borrowed(v_vals_2985_, v_i_2986_);
                    v___x_2992_ = l_Lean_Expr_hash(v_k_2990_);
                    v_h_2993_ = lean_uint64_to_usize(v___x_2992_);
                    v___x_2994_ = 5usize;
                    v___x_2995_ = lean_unsigned_to_nat(1);
                    v___x_2996_ = 1usize;
                    v___x_2997_ = lean_usize_sub(v_depth_2983_, v___x_2996_);
                    v___x_2998_ = lean_usize_mul(v___x_2994_, v___x_2997_);
                    v_h_2999_ = lean_usize_shift_right(v_h_2993_, v___x_2998_);
                    v___x_3000_ = lean_nat_add(v_i_2986_, v___x_2995_);
                    lean_dec(v_i_2986_);
                    lean_inc(v_v_2991_);
                    lean_inc(v_k_2990_);
                    v___x_3001_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_entries_2987_, v_h_2999_, v_depth_2983_, v_k_2990_, v_v_2991_);
                    v_i_2986_ = v___x_3000_;
                    v_entries_2987_ = v___x_3001_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg___boxed(
    mut v_depth_3003_: *mut LeanObject,
    mut v_keys_3004_: *mut LeanObject,
    mut v_vals_3005_: *mut LeanObject,
    mut v_i_3006_: *mut LeanObject,
    mut v_entries_3007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3008_: usize = 0;
    let mut v_res_3009_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3008_ = lean_unbox_usize(v_depth_3003_);
    lean_dec(v_depth_3003_);
    v_res_3009_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_boxed_3008_, v_keys_3004_, v_vals_3005_, v_i_3006_, v_entries_3007_);
    lean_dec_ref(v_vals_3005_);
    lean_dec_ref(v_keys_3004_);
    return v_res_3009_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg___boxed(
    mut v_x_3010_: *mut LeanObject,
    mut v_x_3011_: *mut LeanObject,
    mut v_x_3012_: *mut LeanObject,
    mut v_x_3013_: *mut LeanObject,
    mut v_x_3014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_15932__boxed_3015_: usize = 0;
    let mut v_x_15933__boxed_3016_: usize = 0;
    let mut v_res_3017_: *mut LeanObject = core::ptr::null_mut();
    v_x_15932__boxed_3015_ = lean_unbox_usize(v_x_3011_);
    lean_dec(v_x_3011_);
    v_x_15933__boxed_3016_ = lean_unbox_usize(v_x_3012_);
    lean_dec(v_x_3012_);
    v_res_3017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_3010_, v_x_15932__boxed_3015_, v_x_15933__boxed_3016_, v_x_3013_, v_x_3014_);
    return v_res_3017_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(
    mut v_x_3018_: *mut LeanObject,
    mut v_x_3019_: *mut LeanObject,
    mut v_x_3020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3021_: u64 = 0;
    let mut v___x_3022_: usize = 0;
    let mut v___x_3023_: usize = 0;
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    v___x_3021_ = l_Lean_Expr_hash(v_x_3019_);
    v___x_3022_ = lean_uint64_to_usize(v___x_3021_);
    v___x_3023_ = 1usize;
    v___x_3024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_3018_, v___x_3022_, v___x_3023_, v_x_3019_, v_x_3020_);
    return v___x_3024_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(
    mut v_shouldElimFunDecls_3027_: u8,
    mut v_i_3028_: *mut LeanObject,
    mut v_as_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: usize = 0;
    let mut v___x_3043_: usize = 0;
    let mut v___x_3044_: u8 = 0;
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3057_: u8 = 0;
    let mut v_a_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut v_unused_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut v_reuseFailAlloc_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_a_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v_reuseFailAlloc_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut v_a_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_unused_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3036_ = lean_array_get_size(v_as_3029_);
                v___x_3037_ = lean_nat_dec_lt(v_i_3028_, v___x_3036_);
                if v___x_3037_ == 0 {
                    lean_dec(v_i_3028_);
                    v___x_3038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3038_, 0, v_as_3029_);
                    return v___x_3038_;
                } else {
                    v_a_3039_ = lean_array_fget_borrowed(v_as_3029_, v_i_3028_);
                    if lean_obj_tag(v_a_3039_) == 0 {
                        v_params_3052_ = lean_ctor_get(v_a_3039_, 1);
                        v_code_3053_ = lean_ctor_get(v_a_3039_, 2);
                        v___x_3054_ = lean_st_ref_get(v___y_3030_);
                        v_map_3055_ = lean_ctor_get(v___x_3054_, 0);
                        lean_inc_ref(v_map_3055_);
                        lean_dec(v___x_3054_);
                        v___x_3056_ = 0;
                        v___x_3057_ = 0;
                        lean_inc_ref(v_params_3052_);
                        v___x_3078_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_3056_, v___x_3057_, v_params_3052_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
                        if lean_obj_tag(v___x_3078_) == 0 {
                            v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
                            lean_inc(v_a_3079_);
                            lean_dec_ref_known(v___x_3078_, 1);
                            lean_inc_ref(v_code_3053_);
                            v___x_3080_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_3027_, v_code_3053_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
                            if lean_obj_tag(v___x_3080_) == 0 {
                                v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
                                v_isSharedCheck_3098_ = (!lean_is_exclusive(v___x_3080_)) as u8;
                                if v_isSharedCheck_3098_ == 0 {
                                    v___x_3083_ = v___x_3080_;
                                    v_isShared_3084_ = v_isSharedCheck_3098_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3081_);
                                    lean_dec(v___x_3080_);
                                    v___x_3083_ = lean_box(0);
                                    v_isShared_3084_ = v_isSharedCheck_3098_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3079_);
                                lean_dec_ref(v_as_3029_);
                                lean_dec(v_i_3028_);
                                v_a_3099_ = lean_ctor_get(v___x_3080_, 0);
                                lean_inc(v_a_3099_);
                                lean_dec_ref_known(v___x_3080_, 1);
                                v_a_3059_ = v_a_3099_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_as_3029_);
                            lean_dec(v_i_3028_);
                            v_a_3100_ = lean_ctor_get(v___x_3078_, 0);
                            lean_inc(v_a_3100_);
                            lean_dec_ref_known(v___x_3078_, 1);
                            v_a_3059_ = v_a_3100_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_code_3101_ = lean_ctor_get(v_a_3039_, 0);
                        v___x_3102_ = lean_st_ref_get(v___y_3030_);
                        v_map_3103_ = lean_ctor_get(v___x_3102_, 0);
                        lean_inc_ref(v_map_3103_);
                        lean_dec(v___x_3102_);
                        lean_inc_ref(v_code_3101_);
                        v___x_3104_ =
                            l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(
                                v_shouldElimFunDecls_3027_,
                                v_code_3101_,
                                v___y_3030_,
                                v___y_3031_,
                                v___y_3032_,
                                v___y_3033_,
                                v___y_3034_,
                            );
                        if lean_obj_tag(v___x_3104_) == 0 {
                            v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
                            v_isSharedCheck_3122_ = (!lean_is_exclusive(v___x_3104_)) as u8;
                            if v_isSharedCheck_3122_ == 0 {
                                v___x_3107_ = v___x_3104_;
                                v_isShared_3108_ = v_isSharedCheck_3122_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_3105_);
                                lean_dec(v___x_3104_);
                                v___x_3107_ = lean_box(0);
                                v_isShared_3108_ = v_isSharedCheck_3122_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_as_3029_);
                            lean_dec(v_i_3028_);
                            v_a_3123_ = lean_ctor_get(v___x_3104_, 0);
                            lean_inc(v_a_3123_);
                            lean_dec_ref_known(v___x_3104_, 1);
                            v___x_3124_ = lean_box(0);
                            v___x_3125_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_3030_, v_map_3103_, v___x_3124_);
                            if lean_obj_tag(v___x_3125_) == 0 {
                                v_isSharedCheck_3132_ = (!lean_is_exclusive(v___x_3125_)) as u8;
                                if v_isSharedCheck_3132_ == 0 {
                                    v_unused_3133_ = lean_ctor_get(v___x_3125_, 0);
                                    lean_dec(v_unused_3133_);
                                    v___x_3127_ = v___x_3125_;
                                    v_isShared_3128_ = v_isSharedCheck_3132_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_dec(v___x_3125_);
                                    v___x_3127_ = lean_box(0);
                                    v_isShared_3128_ = v_isSharedCheck_3132_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3123_);
                                v_a_3134_ = lean_ctor_get(v___x_3125_, 0);
                                v_isSharedCheck_3141_ = (!lean_is_exclusive(v___x_3125_)) as u8;
                                if v_isSharedCheck_3141_ == 0 {
                                    v___x_3136_ = v___x_3125_;
                                    v_isShared_3137_ = v_isSharedCheck_3141_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_3134_);
                                    lean_dec(v___x_3125_);
                                    v___x_3136_ = lean_box(0);
                                    v_isShared_3137_ = v_isSharedCheck_3141_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3042_ = lean_ptr_addr(v_a_3039_);
                v___x_3043_ = lean_ptr_addr(v_a_3041_);
                v___x_3044_ = lean_usize_dec_eq(v___x_3042_, v___x_3043_);
                if v___x_3044_ == 0 {
                    v___x_3045_ = lean_unsigned_to_nat(1);
                    v___x_3046_ = lean_nat_add(v_i_3028_, v___x_3045_);
                    v___x_3047_ = lean_array_fset(v_as_3029_, v_i_3028_, v_a_3041_);
                    lean_dec(v_i_3028_);
                    v_i_3028_ = v___x_3046_;
                    v_as_3029_ = v___x_3047_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_a_3041_);
                    v___x_3049_ = lean_unsigned_to_nat(1);
                    v___x_3050_ = lean_nat_add(v_i_3028_, v___x_3049_);
                    lean_dec(v_i_3028_);
                    v_i_3028_ = v___x_3050_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_3060_ = lean_box(0);
                v___x_3061_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_3030_, v_map_3055_, v___x_3060_);
                if lean_obj_tag(v___x_3061_) == 0 {
                    v_isSharedCheck_3068_ = (!lean_is_exclusive(v___x_3061_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v_unused_3069_ = lean_ctor_get(v___x_3061_, 0);
                        lean_dec(v_unused_3069_);
                        v___x_3063_ = v___x_3061_;
                        v_isShared_3064_ = v_isSharedCheck_3068_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_3061_);
                        v___x_3063_ = lean_box(0);
                        v_isShared_3064_ = v_isSharedCheck_3068_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_3059_);
                    v_a_3070_ = lean_ctor_get(v___x_3061_, 0);
                    v_isSharedCheck_3077_ = (!lean_is_exclusive(v___x_3061_)) as u8;
                    if v_isSharedCheck_3077_ == 0 {
                        v___x_3072_ = v___x_3061_;
                        v_isShared_3073_ = v_isSharedCheck_3077_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3070_);
                        lean_dec(v___x_3061_);
                        v___x_3072_ = lean_box(0);
                        v_isShared_3073_ = v_isSharedCheck_3077_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3064_ == 0 {
                    lean_ctor_set_tag(v___x_3063_, 1);
                    lean_ctor_set(v___x_3063_, 0, v_a_3059_);
                    v___x_3066_ = v___x_3063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3059_);
                    v___x_3066_ = v_reuseFailAlloc_3067_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3066_;
            }
            5 => {
                if v_isShared_3073_ == 0 {
                    v___x_3075_ = v___x_3072_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
                    v___x_3075_ = v_reuseFailAlloc_3076_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3075_;
            }
            7 => {
                lean_inc_ref(v_a_3039_);
                v___x_3085_ =
                    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(
                        v___x_3056_,
                        v_a_3039_,
                        v_a_3079_,
                        v_a_3081_,
                    );
                lean_inc_ref(v___x_3085_);
                if v_isShared_3084_ == 0 {
                    lean_ctor_set_tag(v___x_3083_, 1);
                    lean_ctor_set(v___x_3083_, 0, v___x_3085_);
                    v___x_3087_ = v___x_3083_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3085_);
                    v___x_3087_ = v_reuseFailAlloc_3097_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3088_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_3030_, v_map_3055_, v___x_3087_);
                lean_dec_ref(v___x_3087_);
                if lean_obj_tag(v___x_3088_) == 0 {
                    lean_dec_ref_known(v___x_3088_, 1);
                    v_a_3041_ = v___x_3085_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_3085_);
                    lean_dec_ref(v_as_3029_);
                    lean_dec(v_i_3028_);
                    v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
                    v_isSharedCheck_3096_ = (!lean_is_exclusive(v___x_3088_)) as u8;
                    if v_isSharedCheck_3096_ == 0 {
                        v___x_3091_ = v___x_3088_;
                        v_isShared_3092_ = v_isSharedCheck_3096_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3089_);
                        lean_dec(v___x_3088_);
                        v___x_3091_ = lean_box(0);
                        v_isShared_3092_ = v_isSharedCheck_3096_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3092_ == 0 {
                    v___x_3094_ = v___x_3091_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
                    v___x_3094_ = v_reuseFailAlloc_3095_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3094_;
            }
            11 => {
                lean_inc_ref(v_a_3039_);
                v___x_3109_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3039_, v_a_3105_);
                lean_inc_ref(v___x_3109_);
                if v_isShared_3108_ == 0 {
                    lean_ctor_set_tag(v___x_3107_, 1);
                    lean_ctor_set(v___x_3107_, 0, v___x_3109_);
                    v___x_3111_ = v___x_3107_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3109_);
                    v___x_3111_ = v_reuseFailAlloc_3121_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3112_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___lam__0(v___y_3030_, v_map_3103_, v___x_3111_);
                lean_dec_ref(v___x_3111_);
                if lean_obj_tag(v___x_3112_) == 0 {
                    lean_dec_ref_known(v___x_3112_, 1);
                    v_a_3041_ = v___x_3109_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_3109_);
                    lean_dec_ref(v_as_3029_);
                    lean_dec(v_i_3028_);
                    v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
                    v_isSharedCheck_3120_ = (!lean_is_exclusive(v___x_3112_)) as u8;
                    if v_isSharedCheck_3120_ == 0 {
                        v___x_3115_ = v___x_3112_;
                        v_isShared_3116_ = v_isSharedCheck_3120_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3113_);
                        lean_dec(v___x_3112_);
                        v___x_3115_ = lean_box(0);
                        v_isShared_3116_ = v_isSharedCheck_3120_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_3116_ == 0 {
                    v___x_3118_ = v___x_3115_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
                    v___x_3118_ = v_reuseFailAlloc_3119_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3118_;
            }
            15 => {
                if v_isShared_3128_ == 0 {
                    lean_ctor_set_tag(v___x_3127_, 1);
                    lean_ctor_set(v___x_3127_, 0, v_a_3123_);
                    v___x_3130_ = v___x_3127_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3123_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3130_;
            }
            17 => {
                if v_isShared_3137_ == 0 {
                    v___x_3139_ = v___x_3136_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
                    v___x_3139_ = v_reuseFailAlloc_3140_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(
    mut v_shouldElimFunDecls_3142_: u8,
    mut v_code_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: u8 = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: u8 = 0;
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3179_: u8 = 0;
    let mut v___y_3181_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3184_: u8 = 0;
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_unused_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: usize = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: usize = 0;
    let mut v___x_3201_: usize = 0;
    let mut v___x_3202_: u8 = 0;
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_val_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___y_3223_: u8 = 0;
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3233_: u8 = 0;
    let mut v_unused_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: usize = 0;
    let mut v___x_3240_: usize = 0;
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3242_: usize = 0;
    let mut v___x_3243_: usize = 0;
    let mut v___x_3244_: u8 = 0;
    let mut v_isSharedCheck_3245_: u8 = 0;
    let mut v_a_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3249_: u8 = 0;
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v_a_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_decl_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___y_3272_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v_unused_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: usize = 0;
    let mut v___x_3289_: usize = 0;
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v___x_3293_: u8 = 0;
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut v_a_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___y_3319_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3322_: u8 = 0;
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut v_unused_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: usize = 0;
    let mut v___x_3336_: usize = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: usize = 0;
    let mut v___x_3339_: usize = 0;
    let mut v___x_3340_: u8 = 0;
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut v_reuseFailAlloc_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3343_: u8 = 0;
    let mut v_val_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3350_: u8 = 0;
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut v_a_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3358_: u8 = 0;
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3362_: u8 = 0;
    let mut v_decl_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v___y_3373_: u8 = 0;
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v_unused_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: usize = 0;
    let mut v___x_3390_: usize = 0;
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: usize = 0;
    let mut v___x_3393_: usize = 0;
    let mut v___x_3394_: u8 = 0;
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut v_a_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut v_fvarId_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: u8 = 0;
    let mut v___x_3409_: u8 = 0;
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___y_3418_: u8 = 0;
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3421_: u8 = 0;
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut v_unused_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v_isSharedCheck_3438_: u8 = 0;
    let mut v_a_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3455_: u8 = 0;
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v_subst_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: u8 = 0;
    let mut v___x_3486_: u8 = 0;
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: usize = 0;
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: usize = 0;
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: u8 = 0;
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut v_a_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3505_: u8 = 0;
    let mut v_fvarId_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v___x_3515_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_unused_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_code_3143_) {
                    0 => {
                        v_decl_3150_ = lean_ctor_get(v_code_3143_, 0);
                        v_k_3151_ = lean_ctor_get(v_code_3143_, 1);
                        v___x_3152_ = 0;
                        v___x_3153_ = 0;
                        lean_inc_ref(v_decl_3150_);
                        v___x_3154_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v___x_3152_, v___x_3153_, v_decl_3150_, v_a_3144_, v_a_3146_);
                        if lean_obj_tag(v___x_3154_) == 0 {
                            v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
                            lean_inc(v_a_3155_);
                            lean_dec_ref_known(v___x_3154_, 1);
                            v_fvarId_3156_ = lean_ctor_get(v_a_3155_, 0);
                            v_value_3157_ = lean_ctor_get(v_a_3155_, 3);
                            lean_inc(v_value_3157_);
                            v___x_3158_ = l_Lean_Compiler_LCNF_CSE_hasNeverExtract___redArg(
                                v_value_3157_,
                                v_a_3148_,
                            );
                            if lean_obj_tag(v___x_3158_) == 0 {
                                v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
                                lean_inc(v_a_3159_);
                                lean_dec_ref_known(v___x_3158_, 1);
                                v___x_3160_ = (lean_unbox(v_a_3159_) as u8);
                                lean_dec(v_a_3159_);
                                if v___x_3160_ == 0 {
                                    v___x_3161_ = lean_st_ref_get(v_a_3144_);
                                    v_map_3162_ = lean_ctor_get(v___x_3161_, 0);
                                    lean_inc_ref(v_map_3162_);
                                    lean_dec(v___x_3161_);
                                    lean_inc(v_value_3157_);
                                    v___x_3163_ = l_Lean_Compiler_LCNF_LetValue_toExpr(
                                        v___x_3152_,
                                        v_value_3157_,
                                    );
                                    v___x_3164_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_3162_, v___x_3163_);
                                    lean_dec_ref(v_map_3162_);
                                    if lean_obj_tag(v___x_3164_) == 0 {
                                        v___x_3165_ = lean_st_ref_take(v_a_3144_);
                                        v_map_3166_ = lean_ctor_get(v___x_3165_, 0);
                                        v_subst_3167_ = lean_ctor_get(v___x_3165_, 1);
                                        v_isSharedCheck_3205_ =
                                            (!lean_is_exclusive(v___x_3165_)) as u8;
                                        if v_isSharedCheck_3205_ == 0 {
                                            v___x_3169_ = v___x_3165_;
                                            v_isShared_3170_ = v_isSharedCheck_3205_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_subst_3167_);
                                            lean_inc(v_map_3166_);
                                            lean_dec(v___x_3165_);
                                            v___x_3169_ = lean_box(0);
                                            v_isShared_3170_ = v_isSharedCheck_3205_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_inc_ref(v_k_3151_);
                                        lean_dec_ref(v___x_3163_);
                                        lean_dec_ref_known(v_code_3143_, 2);
                                        v_val_3206_ = lean_ctor_get(v___x_3164_, 0);
                                        lean_inc(v_val_3206_);
                                        lean_dec_ref_known(v___x_3164_, 1);
                                        v___x_3207_ = l_Lean_Compiler_LCNF_CSE_replaceLet___redArg(
                                            v_a_3155_,
                                            v_val_3206_,
                                            v_a_3144_,
                                            v_a_3146_,
                                        );
                                        if lean_obj_tag(v___x_3207_) == 0 {
                                            lean_dec_ref_known(v___x_3207_, 1);
                                            v_code_3143_ = v_k_3151_;
                                            state = 0;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_k_3151_);
                                            v_a_3209_ = lean_ctor_get(v___x_3207_, 0);
                                            v_isSharedCheck_3216_ =
                                                (!lean_is_exclusive(v___x_3207_)) as u8;
                                            if v_isSharedCheck_3216_ == 0 {
                                                v___x_3211_ = v___x_3207_;
                                                v_isShared_3212_ = v_isSharedCheck_3216_;
                                                state = 9;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3209_);
                                                lean_dec(v___x_3207_);
                                                v___x_3211_ = lean_box(0);
                                                v_isShared_3212_ = v_isSharedCheck_3216_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_inc_ref(v_k_3151_);
                                    v___x_3217_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_3142_, v_k_3151_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
                                    if lean_obj_tag(v___x_3217_) == 0 {
                                        v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
                                        v_isSharedCheck_3245_ =
                                            (!lean_is_exclusive(v___x_3217_)) as u8;
                                        if v_isSharedCheck_3245_ == 0 {
                                            v___x_3220_ = v___x_3217_;
                                            v_isShared_3221_ = v_isSharedCheck_3245_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3218_);
                                            lean_dec(v___x_3217_);
                                            v___x_3220_ = lean_box(0);
                                            v_isShared_3221_ = v_isSharedCheck_3245_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_3155_);
                                        lean_dec_ref_known(v_code_3143_, 2);
                                        return v___x_3217_;
                                    }
                                }
                            } else {
                                lean_dec(v_a_3155_);
                                lean_dec_ref_known(v_code_3143_, 2);
                                v_a_3246_ = lean_ctor_get(v___x_3158_, 0);
                                v_isSharedCheck_3253_ = (!lean_is_exclusive(v___x_3158_)) as u8;
                                if v_isSharedCheck_3253_ == 0 {
                                    v___x_3248_ = v___x_3158_;
                                    v_isShared_3249_ = v_isSharedCheck_3253_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_3246_);
                                    lean_dec(v___x_3158_);
                                    v___x_3248_ = lean_box(0);
                                    v_isShared_3249_ = v_isSharedCheck_3253_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_3143_, 2);
                            v_a_3254_ = lean_ctor_get(v___x_3154_, 0);
                            v_isSharedCheck_3261_ = (!lean_is_exclusive(v___x_3154_)) as u8;
                            if v_isSharedCheck_3261_ == 0 {
                                v___x_3256_ = v___x_3154_;
                                v_isShared_3257_ = v_isSharedCheck_3261_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_3254_);
                                lean_dec(v___x_3154_);
                                v___x_3256_ = lean_box(0);
                                v_isShared_3257_ = v_isSharedCheck_3261_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_decl_3262_ = lean_ctor_get(v_code_3143_, 0);
                        v_k_3263_ = lean_ctor_get(v_code_3143_, 1);
                        lean_inc_ref(v_decl_3262_);
                        v___x_3264_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_3142_, v_decl_3262_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
                        if lean_obj_tag(v___x_3264_) == 0 {
                            if v_shouldElimFunDecls_3142_ == 0 {
                                v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
                                lean_inc(v_a_3265_);
                                lean_dec_ref_known(v___x_3264_, 1);
                                lean_inc_ref(v_k_3263_);
                                v___x_3266_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_3142_, v_k_3263_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
                                if lean_obj_tag(v___x_3266_) == 0 {
                                    v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                                    v_isSharedCheck_3294_ = (!lean_is_exclusive(v___x_3266_)) as u8;
                                    if v_isSharedCheck_3294_ == 0 {
                                        v___x_3269_ = v___x_3266_;
                                        v_isShared_3270_ = v_isSharedCheck_3294_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3267_);
                                        lean_dec(v___x_3266_);
                                        v___x_3269_ = lean_box(0);
                                        v_isShared_3270_ = v_isSharedCheck_3294_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3265_);
                                    lean_dec_ref_known(v_code_3143_, 2);
                                    return v___x_3266_;
                                }
                            } else {
                                v_a_3295_ = lean_ctor_get(v___x_3264_, 0);
                                lean_inc_n(v_a_3295_, 2);
                                lean_dec_ref_known(v___x_3264_, 1);
                                v___x_3296_ = lean_st_ref_get(v_a_3144_);
                                v_map_3297_ = lean_ctor_get(v___x_3296_, 0);
                                lean_inc_ref(v_map_3297_);
                                lean_dec(v___x_3296_);
                                v___x_3298_ = 0;
                                v___x_3299_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___closed__0;
                                v___x_3300_ = l_Lean_Compiler_LCNF_FunDecl_toExpr(
                                    v___x_3298_,
                                    v_a_3295_,
                                    v___x_3299_,
                                );
                                v___x_3301_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_map_3297_, v___x_3300_);
                                lean_dec_ref(v_map_3297_);
                                if lean_obj_tag(v___x_3301_) == 0 {
                                    v_fvarId_3302_ = lean_ctor_get(v_a_3295_, 0);
                                    v___x_3303_ = lean_st_ref_take(v_a_3144_);
                                    v_map_3304_ = lean_ctor_get(v___x_3303_, 0);
                                    v_subst_3305_ = lean_ctor_get(v___x_3303_, 1);
                                    v_isSharedCheck_3343_ = (!lean_is_exclusive(v___x_3303_)) as u8;
                                    if v_isSharedCheck_3343_ == 0 {
                                        v___x_3307_ = v___x_3303_;
                                        v_isShared_3308_ = v_isSharedCheck_3343_;
                                        state = 27;
                                        continue;
                                    } else {
                                        lean_inc(v_subst_3305_);
                                        lean_inc(v_map_3304_);
                                        lean_dec(v___x_3303_);
                                        v___x_3307_ = lean_box(0);
                                        v_isShared_3308_ = v_isSharedCheck_3343_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    lean_inc_ref(v_k_3263_);
                                    lean_dec_ref(v___x_3300_);
                                    lean_dec_ref_known(v_code_3143_, 2);
                                    v_val_3344_ = lean_ctor_get(v___x_3301_, 0);
                                    lean_inc(v_val_3344_);
                                    lean_dec_ref_known(v___x_3301_, 1);
                                    v___x_3345_ = l_Lean_Compiler_LCNF_CSE_replaceFun___redArg(
                                        v_a_3295_,
                                        v_val_3344_,
                                        v_a_3144_,
                                        v_a_3146_,
                                    );
                                    if lean_obj_tag(v___x_3345_) == 0 {
                                        lean_dec_ref_known(v___x_3345_, 1);
                                        v_code_3143_ = v_k_3263_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_k_3263_);
                                        v_a_3347_ = lean_ctor_get(v___x_3345_, 0);
                                        v_isSharedCheck_3354_ =
                                            (!lean_is_exclusive(v___x_3345_)) as u8;
                                        if v_isSharedCheck_3354_ == 0 {
                                            v___x_3349_ = v___x_3345_;
                                            v_isShared_3350_ = v_isSharedCheck_3354_;
                                            state = 35;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3347_);
                                            lean_dec(v___x_3345_);
                                            v___x_3349_ = lean_box(0);
                                            v_isShared_3350_ = v_isSharedCheck_3354_;
                                            state = 35;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_3143_, 2);
                            v_a_3355_ = lean_ctor_get(v___x_3264_, 0);
                            v_isSharedCheck_3362_ = (!lean_is_exclusive(v___x_3264_)) as u8;
                            if v_isSharedCheck_3362_ == 0 {
                                v___x_3357_ = v___x_3264_;
                                v_isShared_3358_ = v_isSharedCheck_3362_;
                                state = 37;
                                continue;
                            } else {
                                lean_inc(v_a_3355_);
                                lean_dec(v___x_3264_);
                                v___x_3357_ = lean_box(0);
                                v_isShared_3358_ = v_isSharedCheck_3362_;
                                state = 37;
                                continue;
                            }
                        }
                    }
                    2 => {
                        v_decl_3363_ = lean_ctor_get(v_code_3143_, 0);
                        v_k_3364_ = lean_ctor_get(v_code_3143_, 1);
                        lean_inc_ref(v_decl_3363_);
                        v___x_3365_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(v_shouldElimFunDecls_3142_, v_decl_3363_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
                        if lean_obj_tag(v___x_3365_) == 0 {
                            v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
                            lean_inc(v_a_3366_);
                            lean_dec_ref_known(v___x_3365_, 1);
                            lean_inc_ref(v_k_3364_);
                            v___x_3367_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(v_shouldElimFunDecls_3142_, v_k_3364_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
                            if lean_obj_tag(v___x_3367_) == 0 {
                                v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
                                v_isSharedCheck_3395_ = (!lean_is_exclusive(v___x_3367_)) as u8;
                                if v_isSharedCheck_3395_ == 0 {
                                    v___x_3370_ = v___x_3367_;
                                    v_isShared_3371_ = v_isSharedCheck_3395_;
                                    state = 39;
                                    continue;
                                } else {
                                    lean_inc(v_a_3368_);
                                    lean_dec(v___x_3367_);
                                    v___x_3370_ = lean_box(0);
                                    v_isShared_3371_ = v_isSharedCheck_3395_;
                                    state = 39;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3366_);
                                lean_dec_ref_known(v_code_3143_, 2);
                                return v___x_3367_;
                            }
                        } else {
                            lean_dec_ref_known(v_code_3143_, 2);
                            v_a_3396_ = lean_ctor_get(v___x_3365_, 0);
                            v_isSharedCheck_3403_ = (!lean_is_exclusive(v___x_3365_)) as u8;
                            if v_isSharedCheck_3403_ == 0 {
                                v___x_3398_ = v___x_3365_;
                                v_isShared_3399_ = v_isSharedCheck_3403_;
                                state = 45;
                                continue;
                            } else {
                                lean_inc(v_a_3396_);
                                lean_dec(v___x_3365_);
                                v___x_3398_ = lean_box(0);
                                v_isShared_3399_ = v_isSharedCheck_3403_;
                                state = 45;
                                continue;
                            }
                        }
                    }
                    3 => {
                        v_fvarId_3404_ = lean_ctor_get(v_code_3143_, 0);
                        v_args_3405_ = lean_ctor_get(v_code_3143_, 1);
                        v___x_3406_ = lean_st_ref_get(v_a_3144_);
                        v_subst_3407_ = lean_ctor_get(v___x_3406_, 1);
                        lean_inc_ref(v_subst_3407_);
                        lean_dec(v___x_3406_);
                        v___x_3408_ = 0;
                        v___x_3409_ = 0;
                        lean_inc(v_fvarId_3404_);
                        v___x_3410_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_subst_3407_,
                            v_fvarId_3404_,
                            v___x_3409_,
                        );
                        lean_dec_ref(v_subst_3407_);
                        if lean_obj_tag(v___x_3410_) == 0 {
                            v_fvarId_3411_ = lean_ctor_get(v___x_3410_, 0);
                            lean_inc(v_fvarId_3411_);
                            lean_dec_ref_known(v___x_3410_, 1);
                            lean_inc_ref(v_args_3405_);
                            v___x_3412_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v___x_3408_, v___x_3409_, v_args_3405_, v_a_3144_);
                            if lean_obj_tag(v___x_3412_) == 0 {
                                v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
                                v_isSharedCheck_3438_ = (!lean_is_exclusive(v___x_3412_)) as u8;
                                if v_isSharedCheck_3438_ == 0 {
                                    v___x_3415_ = v___x_3412_;
                                    v_isShared_3416_ = v_isSharedCheck_3438_;
                                    state = 47;
                                    continue;
                                } else {
                                    lean_inc(v_a_3413_);
                                    lean_dec(v___x_3412_);
                                    v___x_3415_ = lean_box(0);
                                    v_isShared_3416_ = v_isSharedCheck_3438_;
                                    state = 47;
                                    continue;
                                }
                            } else {
                                lean_dec(v_fvarId_3411_);
                                lean_dec_ref_known(v_code_3143_, 2);
                                v_a_3439_ = lean_ctor_get(v___x_3412_, 0);
                                v_isSharedCheck_3446_ = (!lean_is_exclusive(v___x_3412_)) as u8;
                                if v_isSharedCheck_3446_ == 0 {
                                    v___x_3441_ = v___x_3412_;
                                    v_isShared_3442_ = v_isSharedCheck_3446_;
                                    state = 53;
                                    continue;
                                } else {
                                    lean_inc(v_a_3439_);
                                    lean_dec(v___x_3412_);
                                    v___x_3441_ = lean_box(0);
                                    v_isShared_3442_ = v_isSharedCheck_3446_;
                                    state = 53;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_3143_, 2);
                            v___x_3447_ = l_Lean_Compiler_LCNF_mkReturnErased(
                                v___x_3408_,
                                v_a_3145_,
                                v_a_3146_,
                                v_a_3147_,
                                v_a_3148_,
                            );
                            return v___x_3447_;
                        }
                    }
                    4 => {
                        v_cases_3448_ = lean_ctor_get(v_code_3143_, 0);
                        lean_inc_ref(v_cases_3448_);
                        v_typeName_3449_ = lean_ctor_get(v_cases_3448_, 0);
                        v_resultType_3450_ = lean_ctor_get(v_cases_3448_, 1);
                        v_discr_3451_ = lean_ctor_get(v_cases_3448_, 2);
                        v_alts_3452_ = lean_ctor_get(v_cases_3448_, 3);
                        v_isSharedCheck_3505_ = (!lean_is_exclusive(v_cases_3448_)) as u8;
                        if v_isSharedCheck_3505_ == 0 {
                            v___x_3454_ = v_cases_3448_;
                            v_isShared_3455_ = v_isSharedCheck_3505_;
                            state = 55;
                            continue;
                        } else {
                            lean_inc(v_alts_3452_);
                            lean_inc(v_discr_3451_);
                            lean_inc(v_resultType_3450_);
                            lean_inc(v_typeName_3449_);
                            lean_dec(v_cases_3448_);
                            v___x_3454_ = lean_box(0);
                            v_isShared_3455_ = v_isSharedCheck_3505_;
                            state = 55;
                            continue;
                        }
                    }
                    5 => {
                        v_fvarId_3506_ = lean_ctor_get(v_code_3143_, 0);
                        v___x_3507_ = lean_st_ref_get(v_a_3144_);
                        v_subst_3508_ = lean_ctor_get(v___x_3507_, 1);
                        lean_inc_ref(v_subst_3508_);
                        lean_dec(v___x_3507_);
                        v___x_3509_ = 0;
                        lean_inc(v_fvarId_3506_);
                        v___x_3510_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_subst_3508_,
                            v_fvarId_3506_,
                            v___x_3509_,
                        );
                        lean_dec_ref(v_subst_3508_);
                        if lean_obj_tag(v___x_3510_) == 0 {
                            v_fvarId_3511_ = lean_ctor_get(v___x_3510_, 0);
                            v_isSharedCheck_3530_ = (!lean_is_exclusive(v___x_3510_)) as u8;
                            if v_isSharedCheck_3530_ == 0 {
                                v___x_3513_ = v___x_3510_;
                                v_isShared_3514_ = v_isSharedCheck_3530_;
                                state = 65;
                                continue;
                            } else {
                                lean_inc(v_fvarId_3511_);
                                lean_dec(v___x_3510_);
                                v___x_3513_ = lean_box(0);
                                v_isShared_3514_ = v_isSharedCheck_3530_;
                                state = 65;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_3143_, 1);
                            v___x_3531_ = 0;
                            v___x_3532_ = l_Lean_Compiler_LCNF_mkReturnErased(
                                v___x_3531_,
                                v_a_3145_,
                                v_a_3146_,
                                v_a_3147_,
                                v_a_3148_,
                            );
                            return v___x_3532_;
                        }
                    }
                    _ => {
                        v___x_3533_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3533_, 0, v_code_3143_);
                        return v___x_3533_;
                    }
                }
            }
            1 => {
                lean_inc(v_fvarId_3156_);
                v___x_3171_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_3166_, v___x_3163_, v_fvarId_3156_);
                if v_isShared_3170_ == 0 {
                    lean_ctor_set(v___x_3169_, 0, v___x_3171_);
                    v___x_3173_ = v___x_3169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_subst_3167_);
                    v___x_3173_ = v_reuseFailAlloc_3204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3174_ = lean_st_ref_set(v_a_3144_, v___x_3173_);
                lean_inc_ref(v_k_3151_);
                v___x_3175_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(
                    v_shouldElimFunDecls_3142_,
                    v_k_3151_,
                    v_a_3144_,
                    v_a_3145_,
                    v_a_3146_,
                    v_a_3147_,
                    v_a_3148_,
                );
                if lean_obj_tag(v___x_3175_) == 0 {
                    v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
                    v_isSharedCheck_3203_ = (!lean_is_exclusive(v___x_3175_)) as u8;
                    if v_isSharedCheck_3203_ == 0 {
                        v___x_3178_ = v___x_3175_;
                        v_isShared_3179_ = v_isSharedCheck_3203_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3176_);
                        lean_dec(v___x_3175_);
                        v___x_3178_ = lean_box(0);
                        v_isShared_3179_ = v_isSharedCheck_3203_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3155_);
                    lean_dec_ref_known(v_code_3143_, 2);
                    return v___x_3175_;
                }
            }
            3 => {
                v___x_3197_ = lean_ptr_addr(v_k_3151_);
                v___x_3198_ = lean_ptr_addr(v_a_3176_);
                v___x_3199_ = lean_usize_dec_eq(v___x_3197_, v___x_3198_);
                if v___x_3199_ == 0 {
                    v___y_3181_ = v___x_3199_;
                    state = 4;
                    continue;
                } else {
                    v___x_3200_ = lean_ptr_addr(v_decl_3150_);
                    v___x_3201_ = lean_ptr_addr(v_a_3155_);
                    v___x_3202_ = lean_usize_dec_eq(v___x_3200_, v___x_3201_);
                    v___y_3181_ = v___x_3202_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_3181_ == 0 {
                    v_isSharedCheck_3191_ = (!lean_is_exclusive(v_code_3143_)) as u8;
                    if v_isSharedCheck_3191_ == 0 {
                        v_unused_3192_ = lean_ctor_get(v_code_3143_, 1);
                        lean_dec(v_unused_3192_);
                        v_unused_3193_ = lean_ctor_get(v_code_3143_, 0);
                        lean_dec(v_unused_3193_);
                        v___x_3183_ = v_code_3143_;
                        v_isShared_3184_ = v_isSharedCheck_3191_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_code_3143_);
                        v___x_3183_ = lean_box(0);
                        v_isShared_3184_ = v_isSharedCheck_3191_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3176_);
                    lean_dec(v_a_3155_);
                    if v_isShared_3179_ == 0 {
                        lean_ctor_set(v___x_3178_, 0, v_code_3143_);
                        v___x_3195_ = v___x_3178_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_code_3143_);
                        v___x_3195_ = v_reuseFailAlloc_3196_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3184_ == 0 {
                    lean_ctor_set(v___x_3183_, 1, v_a_3176_);
                    lean_ctor_set(v___x_3183_, 0, v_a_3155_);
                    v___x_3186_ = v___x_3183_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3155_);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_a_3176_);
                    v___x_3186_ = v_reuseFailAlloc_3190_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3179_ == 0 {
                    lean_ctor_set(v___x_3178_, 0, v___x_3186_);
                    v___x_3188_ = v___x_3178_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3186_);
                    v___x_3188_ = v_reuseFailAlloc_3189_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3188_;
            }
            8 => {
                return v___x_3195_;
            }
            9 => {
                if v_isShared_3212_ == 0 {
                    v___x_3214_ = v___x_3211_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
                    v___x_3214_ = v_reuseFailAlloc_3215_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3214_;
            }
            11 => {
                v___x_3239_ = lean_ptr_addr(v_k_3151_);
                v___x_3240_ = lean_ptr_addr(v_a_3218_);
                v___x_3241_ = lean_usize_dec_eq(v___x_3239_, v___x_3240_);
                if v___x_3241_ == 0 {
                    v___y_3223_ = v___x_3241_;
                    state = 12;
                    continue;
                } else {
                    v___x_3242_ = lean_ptr_addr(v_decl_3150_);
                    v___x_3243_ = lean_ptr_addr(v_a_3155_);
                    v___x_3244_ = lean_usize_dec_eq(v___x_3242_, v___x_3243_);
                    v___y_3223_ = v___x_3244_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v___y_3223_ == 0 {
                    v_isSharedCheck_3233_ = (!lean_is_exclusive(v_code_3143_)) as u8;
                    if v_isSharedCheck_3233_ == 0 {
                        v_unused_3234_ = lean_ctor_get(v_code_3143_, 1);
                        lean_dec(v_unused_3234_);
                        v_unused_3235_ = lean_ctor_get(v_code_3143_, 0);
                        lean_dec(v_unused_3235_);
                        v___x_3225_ = v_code_3143_;
                        v_isShared_3226_ = v_isSharedCheck_3233_;
                        state = 13;
                        continue;
                    } else {
                        lean_dec(v_code_3143_);
                        v___x_3225_ = lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3233_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3218_);
                    lean_dec(v_a_3155_);
                    if v_isShared_3221_ == 0 {
                        lean_ctor_set(v___x_3220_, 0, v_code_3143_);
                        v___x_3237_ = v___x_3220_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_code_3143_);
                        v___x_3237_ = v_reuseFailAlloc_3238_;
                        state = 16;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_3226_ == 0 {
                    lean_ctor_set(v___x_3225_, 1, v_a_3218_);
                    lean_ctor_set(v___x_3225_, 0, v_a_3155_);
                    v___x_3228_ = v___x_3225_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3155_);
                    lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_a_3218_);
                    v___x_3228_ = v_reuseFailAlloc_3232_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_3221_ == 0 {
                    lean_ctor_set(v___x_3220_, 0, v___x_3228_);
                    v___x_3230_ = v___x_3220_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3230_;
            }
            16 => {
                return v___x_3237_;
            }
            17 => {
                if v_isShared_3249_ == 0 {
                    v___x_3251_ = v___x_3248_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
                    v___x_3251_ = v_reuseFailAlloc_3252_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3251_;
            }
            19 => {
                if v_isShared_3257_ == 0 {
                    v___x_3259_ = v___x_3256_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
                    v___x_3259_ = v_reuseFailAlloc_3260_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3259_;
            }
            21 => {
                v___x_3288_ = lean_ptr_addr(v_k_3263_);
                v___x_3289_ = lean_ptr_addr(v_a_3267_);
                v___x_3290_ = lean_usize_dec_eq(v___x_3288_, v___x_3289_);
                if v___x_3290_ == 0 {
                    v___y_3272_ = v___x_3290_;
                    state = 22;
                    continue;
                } else {
                    v___x_3291_ = lean_ptr_addr(v_decl_3262_);
                    v___x_3292_ = lean_ptr_addr(v_a_3265_);
                    v___x_3293_ = lean_usize_dec_eq(v___x_3291_, v___x_3292_);
                    v___y_3272_ = v___x_3293_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v___y_3272_ == 0 {
                    v_isSharedCheck_3282_ = (!lean_is_exclusive(v_code_3143_)) as u8;
                    if v_isSharedCheck_3282_ == 0 {
                        v_unused_3283_ = lean_ctor_get(v_code_3143_, 1);
                        lean_dec(v_unused_3283_);
                        v_unused_3284_ = lean_ctor_get(v_code_3143_, 0);
                        lean_dec(v_unused_3284_);
                        v___x_3274_ = v_code_3143_;
                        v_isShared_3275_ = v_isSharedCheck_3282_;
                        state = 23;
                        continue;
                    } else {
                        lean_dec(v_code_3143_);
                        v___x_3274_ = lean_box(0);
                        v_isShared_3275_ = v_isSharedCheck_3282_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3267_);
                    lean_dec(v_a_3265_);
                    if v_isShared_3270_ == 0 {
                        lean_ctor_set(v___x_3269_, 0, v_code_3143_);
                        v___x_3286_ = v___x_3269_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_code_3143_);
                        v___x_3286_ = v_reuseFailAlloc_3287_;
                        state = 26;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_3275_ == 0 {
                    lean_ctor_set(v___x_3274_, 1, v_a_3267_);
                    lean_ctor_set(v___x_3274_, 0, v_a_3265_);
                    v___x_3277_ = v___x_3274_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3265_);
                    lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_a_3267_);
                    v___x_3277_ = v_reuseFailAlloc_3281_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_3270_ == 0 {
                    lean_ctor_set(v___x_3269_, 0, v___x_3277_);
                    v___x_3279_ = v___x_3269_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
                    v___x_3279_ = v_reuseFailAlloc_3280_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3279_;
            }
            26 => {
                return v___x_3286_;
            }
            27 => {
                lean_inc(v_fvarId_3302_);
                v___x_3309_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_map_3304_, v___x_3300_, v_fvarId_3302_);
                if v_isShared_3308_ == 0 {
                    lean_ctor_set(v___x_3307_, 0, v___x_3309_);
                    v___x_3311_ = v___x_3307_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3309_);
                    lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_subst_3305_);
                    v___x_3311_ = v_reuseFailAlloc_3342_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_3312_ = lean_st_ref_set(v_a_3144_, v___x_3311_);
                lean_inc_ref(v_k_3263_);
                v___x_3313_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(
                    v_shouldElimFunDecls_3142_,
                    v_k_3263_,
                    v_a_3144_,
                    v_a_3145_,
                    v_a_3146_,
                    v_a_3147_,
                    v_a_3148_,
                );
                if lean_obj_tag(v___x_3313_) == 0 {
                    v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
                    v_isSharedCheck_3341_ = (!lean_is_exclusive(v___x_3313_)) as u8;
                    if v_isSharedCheck_3341_ == 0 {
                        v___x_3316_ = v___x_3313_;
                        v_isShared_3317_ = v_isSharedCheck_3341_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_3314_);
                        lean_dec(v___x_3313_);
                        v___x_3316_ = lean_box(0);
                        v_isShared_3317_ = v_isSharedCheck_3341_;
                        state = 29;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3295_);
                    lean_dec_ref_known(v_code_3143_, 2);
                    return v___x_3313_;
                }
            }
            29 => {
                v___x_3335_ = lean_ptr_addr(v_k_3263_);
                v___x_3336_ = lean_ptr_addr(v_a_3314_);
                v___x_3337_ = lean_usize_dec_eq(v___x_3335_, v___x_3336_);
                if v___x_3337_ == 0 {
                    v___y_3319_ = v___x_3337_;
                    state = 30;
                    continue;
                } else {
                    v___x_3338_ = lean_ptr_addr(v_decl_3262_);
                    v___x_3339_ = lean_ptr_addr(v_a_3295_);
                    v___x_3340_ = lean_usize_dec_eq(v___x_3338_, v___x_3339_);
                    v___y_3319_ = v___x_3340_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v___y_3319_ == 0 {
                    v_isSharedCheck_3329_ = (!lean_is_exclusive(v_code_3143_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v_unused_3330_ = lean_ctor_get(v_code_3143_, 1);
                        lean_dec(v_unused_3330_);
                        v_unused_3331_ = lean_ctor_get(v_code_3143_, 0);
                        lean_dec(v_unused_3331_);
                        v___x_3321_ = v_code_3143_;
                        v_isShared_3322_ = v_isSharedCheck_3329_;
                        state = 31;
                        continue;
                    } else {
                        lean_dec(v_code_3143_);
                        v___x_3321_ = lean_box(0);
                        v_isShared_3322_ = v_isSharedCheck_3329_;
                        state = 31;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3314_);
                    lean_dec(v_a_3295_);
                    if v_isShared_3317_ == 0 {
                        lean_ctor_set(v___x_3316_, 0, v_code_3143_);
                        v___x_3333_ = v___x_3316_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_code_3143_);
                        v___x_3333_ = v_reuseFailAlloc_3334_;
                        state = 34;
                        continue;
                    }
                }
            }
            31 => {
                if v_isShared_3322_ == 0 {
                    lean_ctor_set(v___x_3321_, 1, v_a_3314_);
                    lean_ctor_set(v___x_3321_, 0, v_a_3295_);
                    v___x_3324_ = v___x_3321_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3295_);
                    lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_a_3314_);
                    v___x_3324_ = v_reuseFailAlloc_3328_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3317_ == 0 {
                    lean_ctor_set(v___x_3316_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3316_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
                    v___x_3326_ = v_reuseFailAlloc_3327_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3326_;
            }
            34 => {
                return v___x_3333_;
            }
            35 => {
                if v_isShared_3350_ == 0 {
                    v___x_3352_ = v___x_3349_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
                    v___x_3352_ = v_reuseFailAlloc_3353_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3352_;
            }
            37 => {
                if v_isShared_3358_ == 0 {
                    v___x_3360_ = v___x_3357_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
                    v___x_3360_ = v_reuseFailAlloc_3361_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3360_;
            }
            39 => {
                v___x_3389_ = lean_ptr_addr(v_k_3364_);
                v___x_3390_ = lean_ptr_addr(v_a_3368_);
                v___x_3391_ = lean_usize_dec_eq(v___x_3389_, v___x_3390_);
                if v___x_3391_ == 0 {
                    v___y_3373_ = v___x_3391_;
                    state = 40;
                    continue;
                } else {
                    v___x_3392_ = lean_ptr_addr(v_decl_3363_);
                    v___x_3393_ = lean_ptr_addr(v_a_3366_);
                    v___x_3394_ = lean_usize_dec_eq(v___x_3392_, v___x_3393_);
                    v___y_3373_ = v___x_3394_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v___y_3373_ == 0 {
                    v_isSharedCheck_3383_ = (!lean_is_exclusive(v_code_3143_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v_unused_3384_ = lean_ctor_get(v_code_3143_, 1);
                        lean_dec(v_unused_3384_);
                        v_unused_3385_ = lean_ctor_get(v_code_3143_, 0);
                        lean_dec(v_unused_3385_);
                        v___x_3375_ = v_code_3143_;
                        v_isShared_3376_ = v_isSharedCheck_3383_;
                        state = 41;
                        continue;
                    } else {
                        lean_dec(v_code_3143_);
                        v___x_3375_ = lean_box(0);
                        v_isShared_3376_ = v_isSharedCheck_3383_;
                        state = 41;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3368_);
                    lean_dec(v_a_3366_);
                    if v_isShared_3371_ == 0 {
                        lean_ctor_set(v___x_3370_, 0, v_code_3143_);
                        v___x_3387_ = v___x_3370_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_code_3143_);
                        v___x_3387_ = v_reuseFailAlloc_3388_;
                        state = 44;
                        continue;
                    }
                }
            }
            41 => {
                if v_isShared_3376_ == 0 {
                    lean_ctor_set(v___x_3375_, 1, v_a_3368_);
                    lean_ctor_set(v___x_3375_, 0, v_a_3366_);
                    v___x_3378_ = v___x_3375_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3366_);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3368_);
                    v___x_3378_ = v_reuseFailAlloc_3382_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_3371_ == 0 {
                    lean_ctor_set(v___x_3370_, 0, v___x_3378_);
                    v___x_3380_ = v___x_3370_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
                    v___x_3380_ = v_reuseFailAlloc_3381_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3380_;
            }
            44 => {
                return v___x_3387_;
            }
            45 => {
                if v_isShared_3399_ == 0 {
                    v___x_3401_ = v___x_3398_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
                    v___x_3401_ = v_reuseFailAlloc_3402_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3401_;
            }
            47 => {
                v___x_3434_ = l_Lean_instBEqFVarId_beq(v_fvarId_3404_, v_fvarId_3411_);
                if v___x_3434_ == 0 {
                    v___y_3418_ = v___x_3434_;
                    state = 48;
                    continue;
                } else {
                    v___x_3435_ = lean_ptr_addr(v_args_3405_);
                    v___x_3436_ = lean_ptr_addr(v_a_3413_);
                    v___x_3437_ = lean_usize_dec_eq(v___x_3435_, v___x_3436_);
                    v___y_3418_ = v___x_3437_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                if v___y_3418_ == 0 {
                    v_isSharedCheck_3428_ = (!lean_is_exclusive(v_code_3143_)) as u8;
                    if v_isSharedCheck_3428_ == 0 {
                        v_unused_3429_ = lean_ctor_get(v_code_3143_, 1);
                        lean_dec(v_unused_3429_);
                        v_unused_3430_ = lean_ctor_get(v_code_3143_, 0);
                        lean_dec(v_unused_3430_);
                        v___x_3420_ = v_code_3143_;
                        v_isShared_3421_ = v_isSharedCheck_3428_;
                        state = 49;
                        continue;
                    } else {
                        lean_dec(v_code_3143_);
                        v___x_3420_ = lean_box(0);
                        v_isShared_3421_ = v_isSharedCheck_3428_;
                        state = 49;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3413_);
                    lean_dec(v_fvarId_3411_);
                    if v_isShared_3416_ == 0 {
                        lean_ctor_set(v___x_3415_, 0, v_code_3143_);
                        v___x_3432_ = v___x_3415_;
                        state = 52;
                        continue;
                    } else {
                        v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_code_3143_);
                        v___x_3432_ = v_reuseFailAlloc_3433_;
                        state = 52;
                        continue;
                    }
                }
            }
            49 => {
                if v_isShared_3421_ == 0 {
                    lean_ctor_set(v___x_3420_, 1, v_a_3413_);
                    lean_ctor_set(v___x_3420_, 0, v_fvarId_3411_);
                    v___x_3423_ = v___x_3420_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3427_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_fvarId_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_a_3413_);
                    v___x_3423_ = v_reuseFailAlloc_3427_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                if v_isShared_3416_ == 0 {
                    lean_ctor_set(v___x_3415_, 0, v___x_3423_);
                    v___x_3425_ = v___x_3415_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
                    v___x_3425_ = v_reuseFailAlloc_3426_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_3425_;
            }
            52 => {
                return v___x_3432_;
            }
            53 => {
                if v_isShared_3442_ == 0 {
                    v___x_3444_ = v___x_3441_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_3444_;
            }
            55 => {
                v___x_3456_ = lean_st_ref_get(v_a_3144_);
                v_subst_3457_ = lean_ctor_get(v___x_3456_, 1);
                lean_inc_ref(v_subst_3457_);
                lean_dec(v___x_3456_);
                v___x_3458_ = 0;
                v___x_3459_ = 0;
                lean_inc(v_discr_3451_);
                v___x_3460_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v_subst_3457_,
                    v_discr_3451_,
                    v___x_3459_,
                );
                lean_dec_ref(v_subst_3457_);
                if lean_obj_tag(v___x_3460_) == 0 {
                    v_fvarId_3461_ = lean_ctor_get(v___x_3460_, 0);
                    v_isSharedCheck_3503_ = (!lean_is_exclusive(v___x_3460_)) as u8;
                    if v_isSharedCheck_3503_ == 0 {
                        v___x_3463_ = v___x_3460_;
                        v_isShared_3464_ = v_isSharedCheck_3503_;
                        state = 56;
                        continue;
                    } else {
                        lean_inc(v_fvarId_3461_);
                        lean_dec(v___x_3460_);
                        v___x_3463_ = lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3503_;
                        state = 56;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3454_);
                    lean_dec_ref(v_alts_3452_);
                    lean_dec(v_discr_3451_);
                    lean_dec_ref(v_resultType_3450_);
                    lean_dec(v_typeName_3449_);
                    lean_dec_ref_known(v_code_3143_, 1);
                    v___x_3504_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v___x_3458_,
                        v_a_3145_,
                        v_a_3146_,
                        v_a_3147_,
                        v_a_3148_,
                    );
                    return v___x_3504_;
                }
            }
            56 => {
                v___x_3465_ = lean_st_ref_get(v_a_3144_);
                v___x_3466_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_3452_);
                v___x_3467_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_3142_, v___x_3466_, v_alts_3452_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
                if lean_obj_tag(v___x_3467_) == 0 {
                    v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
                    v_isSharedCheck_3494_ = (!lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3494_ == 0 {
                        v___x_3470_ = v___x_3467_;
                        v_isShared_3471_ = v_isSharedCheck_3494_;
                        state = 57;
                        continue;
                    } else {
                        lean_inc(v_a_3468_);
                        lean_dec(v___x_3467_);
                        v___x_3470_ = lean_box(0);
                        v_isShared_3471_ = v_isSharedCheck_3494_;
                        state = 57;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3465_);
                    lean_del_object(v___x_3463_);
                    lean_dec(v_fvarId_3461_);
                    lean_del_object(v___x_3454_);
                    lean_dec_ref(v_alts_3452_);
                    lean_dec(v_discr_3451_);
                    lean_dec_ref(v_resultType_3450_);
                    lean_dec(v_typeName_3449_);
                    lean_dec_ref_known(v_code_3143_, 1);
                    v_a_3495_ = lean_ctor_get(v___x_3467_, 0);
                    v_isSharedCheck_3502_ = (!lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3502_ == 0 {
                        v___x_3497_ = v___x_3467_;
                        v_isShared_3498_ = v_isSharedCheck_3502_;
                        state = 63;
                        continue;
                    } else {
                        lean_inc(v_a_3495_);
                        lean_dec(v___x_3467_);
                        v___x_3497_ = lean_box(0);
                        v_isShared_3498_ = v_isSharedCheck_3502_;
                        state = 63;
                        continue;
                    }
                }
            }
            57 => {
                v_subst_3472_ = lean_ctor_get(v___x_3465_, 1);
                lean_inc_ref(v_subst_3472_);
                lean_dec(v___x_3465_);
                lean_inc_ref(v_resultType_3450_);
                v___x_3473_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v___x_3458_,
                        v_subst_3472_,
                        v___x_3459_,
                        v_resultType_3450_,
                    );
                lean_dec_ref(v_subst_3472_);
                v___x_3488_ = lean_ptr_addr(v_alts_3452_);
                lean_dec_ref(v_alts_3452_);
                v___x_3489_ = lean_ptr_addr(v_a_3468_);
                v___x_3490_ = lean_usize_dec_eq(v___x_3488_, v___x_3489_);
                if v___x_3490_ == 0 {
                    lean_dec_ref(v_resultType_3450_);
                    v___y_3485_ = v___x_3490_;
                    state = 62;
                    continue;
                } else {
                    v___x_3491_ = lean_ptr_addr(v_resultType_3450_);
                    lean_dec_ref(v_resultType_3450_);
                    v___x_3492_ = lean_ptr_addr(v___x_3473_);
                    v___x_3493_ = lean_usize_dec_eq(v___x_3491_, v___x_3492_);
                    v___y_3485_ = v___x_3493_;
                    state = 62;
                    continue;
                }
            }
            58 => {
                if v_isShared_3455_ == 0 {
                    lean_ctor_set(v___x_3454_, 3, v_a_3468_);
                    lean_ctor_set(v___x_3454_, 2, v_fvarId_3461_);
                    lean_ctor_set(v___x_3454_, 1, v___x_3473_);
                    v___x_3476_ = v___x_3454_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_typeName_3449_);
                    lean_ctor_set(v_reuseFailAlloc_3483_, 1, v___x_3473_);
                    lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_fvarId_3461_);
                    lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_a_3468_);
                    v___x_3476_ = v_reuseFailAlloc_3483_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_3464_ == 0 {
                    lean_ctor_set_tag(v___x_3463_, 4);
                    lean_ctor_set(v___x_3463_, 0, v___x_3476_);
                    v___x_3478_ = v___x_3463_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_3482_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3476_);
                    v___x_3478_ = v_reuseFailAlloc_3482_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                if v_isShared_3471_ == 0 {
                    lean_ctor_set(v___x_3470_, 0, v___x_3478_);
                    v___x_3480_ = v___x_3470_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
                    v___x_3480_ = v_reuseFailAlloc_3481_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_3480_;
            }
            62 => {
                if v___y_3485_ == 0 {
                    lean_dec(v_discr_3451_);
                    lean_dec_ref_known(v_code_3143_, 1);
                    state = 58;
                    continue;
                } else {
                    v___x_3486_ = l_Lean_instBEqFVarId_beq(v_discr_3451_, v_fvarId_3461_);
                    lean_dec(v_discr_3451_);
                    if v___x_3486_ == 0 {
                        lean_dec_ref_known(v_code_3143_, 1);
                        state = 58;
                        continue;
                    } else {
                        lean_dec_ref(v___x_3473_);
                        lean_del_object(v___x_3470_);
                        lean_dec(v_a_3468_);
                        lean_del_object(v___x_3463_);
                        lean_dec(v_fvarId_3461_);
                        lean_del_object(v___x_3454_);
                        lean_dec(v_typeName_3449_);
                        v___x_3487_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3487_, 0, v_code_3143_);
                        return v___x_3487_;
                    }
                }
            }
            63 => {
                if v_isShared_3498_ == 0 {
                    v___x_3500_ = v___x_3497_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
                    v___x_3500_ = v_reuseFailAlloc_3501_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_3500_;
            }
            65 => {
                v___x_3515_ = l_Lean_instBEqFVarId_beq(v_fvarId_3506_, v_fvarId_3511_);
                if v___x_3515_ == 0 {
                    v_isSharedCheck_3525_ = (!lean_is_exclusive(v_code_3143_)) as u8;
                    if v_isSharedCheck_3525_ == 0 {
                        v_unused_3526_ = lean_ctor_get(v_code_3143_, 0);
                        lean_dec(v_unused_3526_);
                        v___x_3517_ = v_code_3143_;
                        v_isShared_3518_ = v_isSharedCheck_3525_;
                        state = 66;
                        continue;
                    } else {
                        lean_dec(v_code_3143_);
                        v___x_3517_ = lean_box(0);
                        v_isShared_3518_ = v_isSharedCheck_3525_;
                        state = 66;
                        continue;
                    }
                } else {
                    lean_dec(v_fvarId_3511_);
                    if v_isShared_3514_ == 0 {
                        lean_ctor_set(v___x_3513_, 0, v_code_3143_);
                        v___x_3528_ = v___x_3513_;
                        state = 69;
                        continue;
                    } else {
                        v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_code_3143_);
                        v___x_3528_ = v_reuseFailAlloc_3529_;
                        state = 69;
                        continue;
                    }
                }
            }
            66 => {
                if v_isShared_3518_ == 0 {
                    lean_ctor_set(v___x_3517_, 0, v_fvarId_3511_);
                    v___x_3520_ = v___x_3517_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_fvarId_3511_);
                    v___x_3520_ = v_reuseFailAlloc_3524_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                if v_isShared_3514_ == 0 {
                    lean_ctor_set(v___x_3513_, 0, v___x_3520_);
                    v___x_3522_ = v___x_3513_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
                    v___x_3522_ = v_reuseFailAlloc_3523_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_3522_;
            }
            69 => {
                return v___x_3528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(
    mut v_shouldElimFunDecls_3534_: u8,
    mut v_decl_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
    mut v_a_3539_: *mut LeanObject,
    mut v_a_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: u8 = 0;
    let mut v___x_3548_: u8 = 0;
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3558_: u8 = 0;
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut v_reuseFailAlloc_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_a_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3582_: u8 = 0;
    let mut v_unused_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3587_: u8 = 0;
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut v_a_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_3542_ = lean_ctor_get(v_decl_3535_, 2);
                v_type_3543_ = lean_ctor_get(v_decl_3535_, 3);
                v_value_3544_ = lean_ctor_get(v_decl_3535_, 4);
                v___x_3545_ = lean_st_ref_get(v_a_3536_);
                v_subst_3546_ = lean_ctor_get(v___x_3545_, 1);
                lean_inc_ref(v_subst_3546_);
                lean_dec(v___x_3545_);
                v___x_3547_ = 0;
                v___x_3548_ = 0;
                lean_inc_ref(v_type_3543_);
                v___x_3549_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v___x_3547_,
                        v_subst_3546_,
                        v___x_3548_,
                        v_type_3543_,
                    );
                lean_dec_ref(v_subst_3546_);
                lean_inc_ref(v_params_3542_);
                v___x_3550_ = l_Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0(v___x_3547_, v___x_3548_, v_params_3542_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
                if lean_obj_tag(v___x_3550_) == 0 {
                    v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
                    lean_inc(v_a_3551_);
                    lean_dec_ref_known(v___x_3550_, 1);
                    v___x_3552_ = lean_st_ref_get(v_a_3536_);
                    v_map_3553_ = lean_ctor_get(v___x_3552_, 0);
                    lean_inc_ref(v_map_3553_);
                    lean_dec(v___x_3552_);
                    lean_inc_ref(v_value_3544_);
                    v_r_3554_ =
                        l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(
                            v_shouldElimFunDecls_3534_,
                            v_value_3544_,
                            v_a_3536_,
                            v_a_3537_,
                            v_a_3538_,
                            v_a_3539_,
                            v_a_3540_,
                        );
                    if lean_obj_tag(v_r_3554_) == 0 {
                        v_a_3555_ = lean_ctor_get(v_r_3554_, 0);
                        v_isSharedCheck_3572_ = (!lean_is_exclusive(v_r_3554_)) as u8;
                        if v_isSharedCheck_3572_ == 0 {
                            v___x_3557_ = v_r_3554_;
                            v_isShared_3558_ = v_isSharedCheck_3572_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3555_);
                            lean_dec(v_r_3554_);
                            v___x_3557_ = lean_box(0);
                            v_isShared_3558_ = v_isSharedCheck_3572_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3551_);
                        lean_dec_ref(v___x_3549_);
                        lean_dec_ref(v_decl_3535_);
                        v_a_3573_ = lean_ctor_get(v_r_3554_, 0);
                        lean_inc(v_a_3573_);
                        lean_dec_ref_known(v_r_3554_, 1);
                        v___x_3574_ = lean_box(0);
                        v___x_3575_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_3536_, v_map_3553_, v___x_3574_);
                        if lean_obj_tag(v___x_3575_) == 0 {
                            v_isSharedCheck_3582_ = (!lean_is_exclusive(v___x_3575_)) as u8;
                            if v_isSharedCheck_3582_ == 0 {
                                v_unused_3583_ = lean_ctor_get(v___x_3575_, 0);
                                lean_dec(v_unused_3583_);
                                v___x_3577_ = v___x_3575_;
                                v_isShared_3578_ = v_isSharedCheck_3582_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_3575_);
                                v___x_3577_ = lean_box(0);
                                v_isShared_3578_ = v_isSharedCheck_3582_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3573_);
                            v_a_3584_ = lean_ctor_get(v___x_3575_, 0);
                            v_isSharedCheck_3591_ = (!lean_is_exclusive(v___x_3575_)) as u8;
                            if v_isSharedCheck_3591_ == 0 {
                                v___x_3586_ = v___x_3575_;
                                v_isShared_3587_ = v_isSharedCheck_3591_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3584_);
                                lean_dec(v___x_3575_);
                                v___x_3586_ = lean_box(0);
                                v_isShared_3587_ = v_isSharedCheck_3591_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3549_);
                    lean_dec_ref(v_decl_3535_);
                    v_a_3592_ = lean_ctor_get(v___x_3550_, 0);
                    v_isSharedCheck_3599_ = (!lean_is_exclusive(v___x_3550_)) as u8;
                    if v_isSharedCheck_3599_ == 0 {
                        v___x_3594_ = v___x_3550_;
                        v_isShared_3595_ = v_isSharedCheck_3599_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3592_);
                        lean_dec(v___x_3550_);
                        v___x_3594_ = lean_box(0);
                        v_isShared_3595_ = v_isSharedCheck_3599_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_3555_);
                if v_isShared_3558_ == 0 {
                    lean_ctor_set_tag(v___x_3557_, 1);
                    v___x_3560_ = v___x_3557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3555_);
                    v___x_3560_ = v_reuseFailAlloc_3571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3561_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___lam__0(v_a_3536_, v_map_3553_, v___x_3560_);
                lean_dec_ref(v___x_3560_);
                if lean_obj_tag(v___x_3561_) == 0 {
                    lean_dec_ref_known(v___x_3561_, 1);
                    v___x_3562_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3547_, v_decl_3535_, v___x_3549_, v_a_3551_, v_a_3555_, v_a_3538_);
                    return v___x_3562_;
                } else {
                    lean_dec(v_a_3555_);
                    lean_dec(v_a_3551_);
                    lean_dec_ref(v___x_3549_);
                    lean_dec_ref(v_decl_3535_);
                    v_a_3563_ = lean_ctor_get(v___x_3561_, 0);
                    v_isSharedCheck_3570_ = (!lean_is_exclusive(v___x_3561_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v___x_3565_ = v___x_3561_;
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3563_);
                        lean_dec(v___x_3561_);
                        v___x_3565_ = lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3566_ == 0 {
                    v___x_3568_ = v___x_3565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3568_;
            }
            5 => {
                if v_isShared_3578_ == 0 {
                    lean_ctor_set_tag(v___x_3577_, 1);
                    lean_ctor_set(v___x_3577_, 0, v_a_3573_);
                    v___x_3580_ = v___x_3577_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3573_);
                    v___x_3580_ = v_reuseFailAlloc_3581_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3580_;
            }
            7 => {
                if v_isShared_3587_ == 0 {
                    v___x_3589_ = v___x_3586_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
                    v___x_3589_ = v_reuseFailAlloc_3590_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3589_;
            }
            9 => {
                if v_isShared_3595_ == 0 {
                    v___x_3597_ = v___x_3594_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
                    v___x_3597_ = v_reuseFailAlloc_3598_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl___boxed(
    mut v_shouldElimFunDecls_3600_: *mut LeanObject,
    mut v_decl_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
    mut v_a_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldElimFunDecls_boxed_3608_: u8 = 0;
    let mut v_res_3609_: *mut LeanObject = core::ptr::null_mut();
    v_shouldElimFunDecls_boxed_3608_ = (lean_unbox(v_shouldElimFunDecls_3600_) as u8);
    v_res_3609_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl(
        v_shouldElimFunDecls_boxed_3608_,
        v_decl_3601_,
        v_a_3602_,
        v_a_3603_,
        v_a_3604_,
        v_a_3605_,
        v_a_3606_,
    );
    lean_dec(v_a_3606_);
    lean_dec_ref(v_a_3605_);
    lean_dec(v_a_3604_);
    lean_dec_ref(v_a_3603_);
    lean_dec(v_a_3602_);
    return v_res_3609_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6___boxed(
    mut v_shouldElimFunDecls_3610_: *mut LeanObject,
    mut v_i_3611_: *mut LeanObject,
    mut v_as_3612_: *mut LeanObject,
    mut v___y_3613_: *mut LeanObject,
    mut v___y_3614_: *mut LeanObject,
    mut v___y_3615_: *mut LeanObject,
    mut v___y_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldElimFunDecls_boxed_3619_: u8 = 0;
    let mut v_res_3620_: *mut LeanObject = core::ptr::null_mut();
    v_shouldElimFunDecls_boxed_3619_ = (lean_unbox(v_shouldElimFunDecls_3610_) as u8);
    v_res_3620_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__6(v_shouldElimFunDecls_boxed_3619_, v_i_3611_, v_as_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
    lean_dec(v___y_3617_);
    lean_dec_ref(v___y_3616_);
    lean_dec(v___y_3615_);
    lean_dec_ref(v___y_3614_);
    lean_dec(v___y_3613_);
    return v_res_3620_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go___boxed(
    mut v_shouldElimFunDecls_3621_: *mut LeanObject,
    mut v_code_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
    mut v_a_3625_: *mut LeanObject,
    mut v_a_3626_: *mut LeanObject,
    mut v_a_3627_: *mut LeanObject,
    mut v_a_3628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldElimFunDecls_boxed_3629_: u8 = 0;
    let mut v_res_3630_: *mut LeanObject = core::ptr::null_mut();
    v_shouldElimFunDecls_boxed_3629_ = (lean_unbox(v_shouldElimFunDecls_3621_) as u8);
    v_res_3630_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(
        v_shouldElimFunDecls_boxed_3629_,
        v_code_3622_,
        v_a_3623_,
        v_a_3624_,
        v_a_3625_,
        v_a_3626_,
        v_a_3627_,
    );
    lean_dec(v_a_3627_);
    lean_dec_ref(v_a_3626_);
    lean_dec(v_a_3625_);
    lean_dec_ref(v_a_3624_);
    lean_dec(v_a_3623_);
    return v_res_3630_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(
    mut v_pu_3631_: u8,
    mut v_t_3632_: u8,
    mut v_decl_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    v___x_3640_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___redArg(v_pu_3631_, v_t_3632_, v_decl_3633_, v___y_3634_, v___y_3636_);
    return v___x_3640_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2___boxed(
    mut v_pu_3641_: *mut LeanObject,
    mut v_t_3642_: *mut LeanObject,
    mut v_decl_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3650_: u8 = 0;
    let mut v_t_boxed_3651_: u8 = 0;
    let mut v_res_3652_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3650_ = (lean_unbox(v_pu_3641_) as u8);
    v_t_boxed_3651_ = (lean_unbox(v_t_3642_) as u8);
    v_res_3652_ = l_Lean_Compiler_LCNF_normLetDecl___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__2(v_pu_boxed_3650_, v_t_boxed_3651_, v_decl_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
    lean_dec(v___y_3648_);
    lean_dec_ref(v___y_3647_);
    lean_dec(v___y_3646_);
    lean_dec_ref(v___y_3645_);
    lean_dec(v___y_3644_);
    return v_res_3652_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(
    mut v_pu_3653_: u8,
    mut v_t_3654_: u8,
    mut v_args_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    v___x_3662_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___redArg(v_pu_3653_, v_t_3654_, v_args_3655_, v___y_3656_);
    return v___x_3662_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5___boxed(
    mut v_pu_3663_: *mut LeanObject,
    mut v_t_3664_: *mut LeanObject,
    mut v_args_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
    mut v___y_3671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3672_: u8 = 0;
    let mut v_t_boxed_3673_: u8 = 0;
    let mut v_res_3674_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3672_ = (lean_unbox(v_pu_3663_) as u8);
    v_t_boxed_3673_ = (lean_unbox(v_t_3664_) as u8);
    v_res_3674_ = l_Lean_Compiler_LCNF_normArgs___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__5(v_pu_boxed_3672_, v_t_boxed_3673_, v_args_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
    lean_dec(v___y_3670_);
    lean_dec_ref(v___y_3669_);
    lean_dec(v___y_3668_);
    lean_dec_ref(v___y_3667_);
    lean_dec(v___y_3666_);
    return v_res_3674_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(
    mut v_00_u03b2_3675_: *mut LeanObject,
    mut v_x_3676_: *mut LeanObject,
    mut v_x_3677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    v___x_3678_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___redArg(v_x_3676_, v_x_3677_);
    return v___x_3678_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3___boxed(
    mut v_00_u03b2_3679_: *mut LeanObject,
    mut v_x_3680_: *mut LeanObject,
    mut v_x_3681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3682_: *mut LeanObject = core::ptr::null_mut();
    v_res_3682_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3(v_00_u03b2_3679_, v_x_3680_, v_x_3681_);
    lean_dec_ref(v_x_3681_);
    lean_dec_ref(v_x_3680_);
    return v_res_3682_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4(
    mut v_00_u03b2_3683_: *mut LeanObject,
    mut v_x_3684_: *mut LeanObject,
    mut v_x_3685_: *mut LeanObject,
    mut v_x_3686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4___redArg(v_x_3684_, v_x_3685_, v_x_3686_);
    return v___x_3687_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(
    mut v_pu_3688_: u8,
    mut v_t_3689_: u8,
    mut v_i_3690_: *mut LeanObject,
    mut v_as_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
    mut v___y_3694_: *mut LeanObject,
    mut v___y_3695_: *mut LeanObject,
    mut v___y_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3698_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___redArg(v_pu_3688_, v_t_3689_, v_i_3690_, v_as_3691_, v___y_3692_, v___y_3694_);
    return v___x_3698_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0___boxed(
    mut v_pu_3699_: *mut LeanObject,
    mut v_t_3700_: *mut LeanObject,
    mut v_i_3701_: *mut LeanObject,
    mut v_as_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3709_: u8 = 0;
    let mut v_t_boxed_3710_: u8 = 0;
    let mut v_res_3711_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3709_ = (lean_unbox(v_pu_3699_) as u8);
    v_t_boxed_3710_ = (lean_unbox(v_t_3700_) as u8);
    v_res_3711_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_goFunDecl_spec__0_spec__0(v_pu_boxed_3709_, v_t_boxed_3710_, v_i_3701_, v_as_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
    lean_dec(v___y_3707_);
    lean_dec_ref(v___y_3706_);
    lean_dec(v___y_3705_);
    lean_dec_ref(v___y_3704_);
    lean_dec(v___y_3703_);
    return v_res_3711_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(
    mut v_00_u03b2_3712_: *mut LeanObject,
    mut v_x_3713_: *mut LeanObject,
    mut v_x_3714_: usize,
    mut v_x_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    v___x_3716_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___redArg(v_x_3713_, v_x_3714_, v_x_3715_);
    return v___x_3716_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4___boxed(
    mut v_00_u03b2_3717_: *mut LeanObject,
    mut v_x_3718_: *mut LeanObject,
    mut v_x_3719_: *mut LeanObject,
    mut v_x_3720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17291__boxed_3721_: usize = 0;
    let mut v_res_3722_: *mut LeanObject = core::ptr::null_mut();
    v_x_17291__boxed_3721_ = lean_unbox_usize(v_x_3719_);
    lean_dec(v_x_3719_);
    v_res_3722_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4(v_00_u03b2_3717_, v_x_3718_, v_x_17291__boxed_3721_, v_x_3720_);
    lean_dec_ref(v_x_3720_);
    lean_dec_ref(v_x_3718_);
    return v_res_3722_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(
    mut v_00_u03b2_3723_: *mut LeanObject,
    mut v_x_3724_: *mut LeanObject,
    mut v_x_3725_: usize,
    mut v_x_3726_: usize,
    mut v_x_3727_: *mut LeanObject,
    mut v_x_3728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___redArg(v_x_3724_, v_x_3725_, v_x_3726_, v_x_3727_, v_x_3728_);
    return v___x_3729_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6___boxed(
    mut v_00_u03b2_3730_: *mut LeanObject,
    mut v_x_3731_: *mut LeanObject,
    mut v_x_3732_: *mut LeanObject,
    mut v_x_3733_: *mut LeanObject,
    mut v_x_3734_: *mut LeanObject,
    mut v_x_3735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17302__boxed_3736_: usize = 0;
    let mut v_x_17303__boxed_3737_: usize = 0;
    let mut v_res_3738_: *mut LeanObject = core::ptr::null_mut();
    v_x_17302__boxed_3736_ = lean_unbox_usize(v_x_3732_);
    lean_dec(v_x_3732_);
    v_x_17303__boxed_3737_ = lean_unbox_usize(v_x_3733_);
    lean_dec(v_x_3733_);
    v_res_3738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6(v_00_u03b2_3730_, v_x_3731_, v_x_17302__boxed_3736_, v_x_17303__boxed_3737_, v_x_3734_, v_x_3735_);
    return v_res_3738_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(
    mut v_00_u03b2_3739_: *mut LeanObject,
    mut v_keys_3740_: *mut LeanObject,
    mut v_vals_3741_: *mut LeanObject,
    mut v_heq_3742_: *mut LeanObject,
    mut v_i_3743_: *mut LeanObject,
    mut v_k_3744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___redArg(v_keys_3740_, v_vals_3741_, v_i_3743_, v_k_3744_);
    return v___x_3745_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_3746_: *mut LeanObject,
    mut v_keys_3747_: *mut LeanObject,
    mut v_vals_3748_: *mut LeanObject,
    mut v_heq_3749_: *mut LeanObject,
    mut v_i_3750_: *mut LeanObject,
    mut v_k_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3752_: *mut LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__3_spec__4_spec__6(v_00_u03b2_3746_, v_keys_3747_, v_vals_3748_, v_heq_3749_, v_i_3750_, v_k_3751_);
    lean_dec_ref(v_k_3751_);
    lean_dec_ref(v_vals_3748_);
    lean_dec_ref(v_keys_3747_);
    return v_res_3752_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9(
    mut v_00_u03b2_3753_: *mut LeanObject,
    mut v_n_3754_: *mut LeanObject,
    mut v_k_3755_: *mut LeanObject,
    mut v_v_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    v___x_3757_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9___redArg(v_n_3754_, v_k_3755_, v_v_3756_);
    return v___x_3757_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(
    mut v_00_u03b2_3758_: *mut LeanObject,
    mut v_depth_3759_: usize,
    mut v_keys_3760_: *mut LeanObject,
    mut v_vals_3761_: *mut LeanObject,
    mut v_heq_3762_: *mut LeanObject,
    mut v_i_3763_: *mut LeanObject,
    mut v_entries_3764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    v___x_3765_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___redArg(v_depth_3759_, v_keys_3760_, v_vals_3761_, v_i_3763_, v_entries_3764_);
    return v___x_3765_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10___boxed(
    mut v_00_u03b2_3766_: *mut LeanObject,
    mut v_depth_3767_: *mut LeanObject,
    mut v_keys_3768_: *mut LeanObject,
    mut v_vals_3769_: *mut LeanObject,
    mut v_heq_3770_: *mut LeanObject,
    mut v_i_3771_: *mut LeanObject,
    mut v_entries_3772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3773_: usize = 0;
    let mut v_res_3774_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3773_ = lean_unbox_usize(v_depth_3767_);
    lean_dec(v_depth_3767_);
    v_res_3774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__10(v_00_u03b2_3766_, v_depth_boxed_3773_, v_keys_3768_, v_vals_3769_, v_heq_3770_, v_i_3771_, v_entries_3772_);
    lean_dec_ref(v_vals_3769_);
    lean_dec_ref(v_keys_3768_);
    return v_res_3774_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11(
    mut v_00_u03b2_3775_: *mut LeanObject,
    mut v_x_3776_: *mut LeanObject,
    mut v_x_3777_: *mut LeanObject,
    mut v_x_3778_: *mut LeanObject,
    mut v_x_3779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    v___x_3780_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go_spec__4_spec__6_spec__9_spec__11___redArg(v_x_3776_, v_x_3777_, v_x_3778_, v_x_3779_);
    return v___x_3780_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_cse___closed__0() -> *mut LeanObject {
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    v___x_3781_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3781_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_cse___closed__1() -> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Code_cse___closed__0,
    );
    v___x_3783_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3783_, 0, v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_cse___closed__2() -> *mut LeanObject {
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3784_ = lean_box(0);
    v___x_3785_ = lean_unsigned_to_nat(16);
    v___x_3786_ = lean_mk_array(v___x_3785_, v___x_3784_);
    return v___x_3786_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_cse___closed__3() -> *mut LeanObject {
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    v___x_3787_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__2_once),
        _init_l_Lean_Compiler_LCNF_Code_cse___closed__2,
    );
    v___x_3788_ = lean_unsigned_to_nat(0);
    v___x_3789_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3789_, 0, v___x_3788_);
    lean_ctor_set(v___x_3789_, 1, v___x_3787_);
    return v___x_3789_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_cse___closed__4() -> *mut LeanObject {
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    v___x_3790_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__3_once),
        _init_l_Lean_Compiler_LCNF_Code_cse___closed__3,
    );
    v___x_3791_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__1_once),
        _init_l_Lean_Compiler_LCNF_Code_cse___closed__1,
    );
    v___x_3792_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3792_, 0, v___x_3791_);
    lean_ctor_set(v___x_3792_, 1, v___x_3790_);
    return v___x_3792_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_cse(
    mut v_shouldElimFunDecls_3793_: u8,
    mut v_code_3794_: *mut LeanObject,
    mut v_a_3795_: *mut LeanObject,
    mut v_a_3796_: *mut LeanObject,
    mut v_a_3797_: *mut LeanObject,
    mut v_a_3798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3800_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_cse___closed__4_once),
                    _init_l_Lean_Compiler_LCNF_Code_cse___closed__4,
                );
                v___x_3801_ = lean_st_mk_ref(v___x_3800_);
                v___x_3802_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_Code_cse_go(
                    v_shouldElimFunDecls_3793_,
                    v_code_3794_,
                    v___x_3801_,
                    v_a_3795_,
                    v_a_3796_,
                    v_a_3797_,
                    v_a_3798_,
                );
                if lean_obj_tag(v___x_3802_) == 0 {
                    v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
                    v_isSharedCheck_3811_ = (!lean_is_exclusive(v___x_3802_)) as u8;
                    if v_isSharedCheck_3811_ == 0 {
                        v___x_3805_ = v___x_3802_;
                        v_isShared_3806_ = v_isSharedCheck_3811_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3803_);
                        lean_dec(v___x_3802_);
                        v___x_3805_ = lean_box(0);
                        v_isShared_3806_ = v_isSharedCheck_3811_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3801_);
                    return v___x_3802_;
                }
            }
            1 => {
                v___x_3807_ = lean_st_ref_get(v___x_3801_);
                lean_dec(v___x_3801_);
                lean_dec(v___x_3807_);
                if v_isShared_3806_ == 0 {
                    v___x_3809_ = v___x_3805_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3803_);
                    v___x_3809_ = v_reuseFailAlloc_3810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_cse___boxed(
    mut v_shouldElimFunDecls_3812_: *mut LeanObject,
    mut v_code_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldElimFunDecls_boxed_3819_: u8 = 0;
    let mut v_res_3820_: *mut LeanObject = core::ptr::null_mut();
    v_shouldElimFunDecls_boxed_3819_ = (lean_unbox(v_shouldElimFunDecls_3812_) as u8);
    v_res_3820_ = l_Lean_Compiler_LCNF_Code_cse(
        v_shouldElimFunDecls_boxed_3819_,
        v_code_3813_,
        v_a_3814_,
        v_a_3815_,
        v_a_3816_,
        v_a_3817_,
    );
    lean_dec(v_a_3817_);
    lean_dec_ref(v_a_3816_);
    lean_dec(v_a_3815_);
    lean_dec_ref(v_a_3814_);
    return v_res_3820_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(
    mut v_f_3821_: *mut LeanObject,
    mut v_v_3822_: *mut LeanObject,
    mut v___y_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_a_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_3822_) == 0 {
                    v_code_3828_ = lean_ctor_get(v_v_3822_, 0);
                    v_isSharedCheck_3852_ = (!lean_is_exclusive(v_v_3822_)) as u8;
                    if v_isSharedCheck_3852_ == 0 {
                        v___x_3830_ = v_v_3822_;
                        v_isShared_3831_ = v_isSharedCheck_3852_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_3828_);
                        lean_dec(v_v_3822_);
                        v___x_3830_ = lean_box(0);
                        v_isShared_3831_ = v_isSharedCheck_3852_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_3821_);
                    v___x_3853_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3853_, 0, v_v_3822_);
                    return v___x_3853_;
                }
            }
            1 => {
                lean_inc(v___y_3826_);
                lean_inc_ref(v___y_3825_);
                lean_inc(v___y_3824_);
                lean_inc_ref(v___y_3823_);
                v___x_3832_ = lean_apply_6(
                    v_f_3821_,
                    v_code_3828_,
                    v___y_3823_,
                    v___y_3824_,
                    v___y_3825_,
                    v___y_3826_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3832_) == 0 {
                    v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
                    v_isSharedCheck_3843_ = (!lean_is_exclusive(v___x_3832_)) as u8;
                    if v_isSharedCheck_3843_ == 0 {
                        v___x_3835_ = v___x_3832_;
                        v_isShared_3836_ = v_isSharedCheck_3843_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3833_);
                        lean_dec(v___x_3832_);
                        v___x_3835_ = lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3843_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3830_);
                    v_a_3844_ = lean_ctor_get(v___x_3832_, 0);
                    v_isSharedCheck_3851_ = (!lean_is_exclusive(v___x_3832_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v___x_3846_ = v___x_3832_;
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3844_);
                        lean_dec(v___x_3832_);
                        v___x_3846_ = lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3831_ == 0 {
                    lean_ctor_set(v___x_3830_, 0, v_a_3833_);
                    v___x_3838_ = v___x_3830_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3833_);
                    v___x_3838_ = v_reuseFailAlloc_3842_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3836_ == 0 {
                    lean_ctor_set(v___x_3835_, 0, v___x_3838_);
                    v___x_3840_ = v___x_3835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
                    v___x_3840_ = v_reuseFailAlloc_3841_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3840_;
            }
            5 => {
                if v_isShared_3847_ == 0 {
                    v___x_3849_ = v___x_3846_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
                    v___x_3849_ = v_reuseFailAlloc_3850_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg___boxed(
    mut v_f_3854_: *mut LeanObject,
    mut v_v_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3861_: *mut LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_3854_, v_v_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
    lean_dec(v___y_3859_);
    lean_dec_ref(v___y_3858_);
    lean_dec(v___y_3857_);
    lean_dec_ref(v___y_3856_);
    return v_res_3861_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(
    mut v_pu_3862_: u8,
    mut v_f_3863_: *mut LeanObject,
    mut v_v_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
    mut v___y_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    v___x_3870_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v_f_3863_, v_v_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
    return v___x_3870_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___boxed(
    mut v_pu_3871_: *mut LeanObject,
    mut v_f_3872_: *mut LeanObject,
    mut v_v_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
    mut v___y_3875_: *mut LeanObject,
    mut v___y_3876_: *mut LeanObject,
    mut v___y_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3879_ = (lean_unbox(v_pu_3871_) as u8);
    v_res_3880_ =
        l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0(
            v_pu_boxed_3879_,
            v_f_3872_,
            v_v_3873_,
            v___y_3874_,
            v___y_3875_,
            v___y_3876_,
            v___y_3877_,
        );
    lean_dec(v___y_3877_);
    lean_dec_ref(v___y_3876_);
    lean_dec(v___y_3875_);
    lean_dec_ref(v___y_3874_);
    return v_res_3880_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_cse___lam__0(
    mut v_shouldElimFunDecls_3881_: u8,
    mut v_x_3882_: *mut LeanObject,
    mut v___y_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    v___x_3888_ = l_Lean_Compiler_LCNF_Code_cse(
        v_shouldElimFunDecls_3881_,
        v_x_3882_,
        v___y_3883_,
        v___y_3884_,
        v___y_3885_,
        v___y_3886_,
    );
    return v___x_3888_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed(
    mut v_shouldElimFunDecls_3889_: *mut LeanObject,
    mut v_x_3890_: *mut LeanObject,
    mut v___y_3891_: *mut LeanObject,
    mut v___y_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldElimFunDecls_boxed_3896_: u8 = 0;
    let mut v_res_3897_: *mut LeanObject = core::ptr::null_mut();
    v_shouldElimFunDecls_boxed_3896_ = (lean_unbox(v_shouldElimFunDecls_3889_) as u8);
    v_res_3897_ = l_Lean_Compiler_LCNF_Decl_cse___lam__0(
        v_shouldElimFunDecls_boxed_3896_,
        v_x_3890_,
        v___y_3891_,
        v___y_3892_,
        v___y_3893_,
        v___y_3894_,
    );
    lean_dec(v___y_3894_);
    lean_dec_ref(v___y_3893_);
    lean_dec(v___y_3892_);
    lean_dec_ref(v___y_3891_);
    return v_res_3897_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_cse(
    mut v_shouldElimFunDecls_3898_: u8,
    mut v_decl_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
    mut v_a_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_3907_: u8 = 0;
    let mut v_inlineAttr_x3f_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3911_: u8 = 0;
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v_a_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3929_: u8 = 0;
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_3905_ = lean_ctor_get(v_decl_3899_, 0);
                v_value_3906_ = lean_ctor_get(v_decl_3899_, 1);
                v_recursive_3907_ = lean_ctor_get_uint8(
                    v_decl_3899_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_3908_ = lean_ctor_get(v_decl_3899_, 2);
                v_isSharedCheck_3934_ = (!lean_is_exclusive(v_decl_3899_)) as u8;
                if v_isSharedCheck_3934_ == 0 {
                    v___x_3910_ = v_decl_3899_;
                    v_isShared_3911_ = v_isSharedCheck_3934_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_3908_);
                    lean_inc(v_value_3906_);
                    lean_inc(v_toSignature_3905_);
                    lean_dec(v_decl_3899_);
                    v___x_3910_ = lean_box(0);
                    v_isShared_3911_ = v_isSharedCheck_3934_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3912_ = lean_box((v_shouldElimFunDecls_3898_) as usize);
                v___f_3913_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Decl_cse___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    1,
                );
                lean_closure_set(v___f_3913_, 0, v___x_3912_);
                v___x_3914_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_cse_spec__0___redArg(v___f_3913_, v_value_3906_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_);
                if lean_obj_tag(v___x_3914_) == 0 {
                    v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
                    v_isSharedCheck_3925_ = (!lean_is_exclusive(v___x_3914_)) as u8;
                    if v_isSharedCheck_3925_ == 0 {
                        v___x_3917_ = v___x_3914_;
                        v_isShared_3918_ = v_isSharedCheck_3925_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3915_);
                        lean_dec(v___x_3914_);
                        v___x_3917_ = lean_box(0);
                        v_isShared_3918_ = v_isSharedCheck_3925_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3910_);
                    lean_dec(v_inlineAttr_x3f_3908_);
                    lean_dec_ref(v_toSignature_3905_);
                    v_a_3926_ = lean_ctor_get(v___x_3914_, 0);
                    v_isSharedCheck_3933_ = (!lean_is_exclusive(v___x_3914_)) as u8;
                    if v_isSharedCheck_3933_ == 0 {
                        v___x_3928_ = v___x_3914_;
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3926_);
                        lean_dec(v___x_3914_);
                        v___x_3928_ = lean_box(0);
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3911_ == 0 {
                    lean_ctor_set(v___x_3910_, 1, v_a_3915_);
                    v___x_3920_ = v___x_3910_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_toSignature_3905_);
                    lean_ctor_set(v_reuseFailAlloc_3924_, 1, v_a_3915_);
                    lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_inlineAttr_x3f_3908_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3924_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_3907_,
                    );
                    v___x_3920_ = v_reuseFailAlloc_3924_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3918_ == 0 {
                    lean_ctor_set(v___x_3917_, 0, v___x_3920_);
                    v___x_3922_ = v___x_3917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3922_;
            }
            5 => {
                if v_isShared_3929_ == 0 {
                    v___x_3931_ = v___x_3928_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
                    v___x_3931_ = v_reuseFailAlloc_3932_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_cse___boxed(
    mut v_shouldElimFunDecls_3935_: *mut LeanObject,
    mut v_decl_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldElimFunDecls_boxed_3942_: u8 = 0;
    let mut v_res_3943_: *mut LeanObject = core::ptr::null_mut();
    v_shouldElimFunDecls_boxed_3942_ = (lean_unbox(v_shouldElimFunDecls_3935_) as u8);
    v_res_3943_ = l_Lean_Compiler_LCNF_Decl_cse(
        v_shouldElimFunDecls_boxed_3942_,
        v_decl_3936_,
        v_a_3937_,
        v_a_3938_,
        v_a_3939_,
        v_a_3940_,
    );
    lean_dec(v_a_3940_);
    lean_dec_ref(v_a_3939_);
    lean_dec(v_a_3938_);
    lean_dec_ref(v_a_3937_);
    return v_res_3943_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cse___lam__0(
    mut v_shouldElimFunDecls_3947_: u8,
    mut v_phase_3948_: u8,
    mut v_occurrence_3949_: *mut LeanObject,
    mut v_h_3950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_Lean_Compiler_LCNF_cse___lam__0___closed__1;
    v___x_3952_ = lean_box((v_shouldElimFunDecls_3947_) as usize);
    v___x_3953_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Decl_cse___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___x_3953_, 0, v___x_3952_);
    v___x_3954_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_3951_,
        v_phase_3948_,
        v___x_3953_,
        v_occurrence_3949_,
    );
    return v___x_3954_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cse___lam__0___boxed(
    mut v_shouldElimFunDecls_3955_: *mut LeanObject,
    mut v_phase_3956_: *mut LeanObject,
    mut v_occurrence_3957_: *mut LeanObject,
    mut v_h_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldElimFunDecls_boxed_3959_: u8 = 0;
    let mut v_phase_boxed_3960_: u8 = 0;
    let mut v_res_3961_: *mut LeanObject = core::ptr::null_mut();
    v_shouldElimFunDecls_boxed_3959_ = (lean_unbox(v_shouldElimFunDecls_3955_) as u8);
    v_phase_boxed_3960_ = (lean_unbox(v_phase_3956_) as u8);
    v_res_3961_ = l_Lean_Compiler_LCNF_cse___lam__0(
        v_shouldElimFunDecls_boxed_3959_,
        v_phase_boxed_3960_,
        v_occurrence_3957_,
        v_h_3958_,
    );
    return v_res_3961_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cse(
    mut v_phase_3962_: u8,
    mut v_shouldElimFunDecls_3963_: u8,
    mut v_occurrence_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    v___x_3965_ = lean_box((v_shouldElimFunDecls_3963_) as usize);
    v___x_3966_ = lean_box((v_phase_3962_) as usize);
    v___f_3967_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_cse___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3967_, 0, v___x_3965_);
    lean_closure_set(v___f_3967_, 1, v___x_3966_);
    lean_closure_set(v___f_3967_, 2, v_occurrence_3964_);
    v___x_3968_ = l_Lean_Compiler_LCNF_instInhabitedPass;
    v___x_3969_ = 0;
    v___x_3970_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
        v___x_3968_,
        v_phase_3962_,
        v___x_3969_,
        v___f_3967_,
    );
    return v___x_3970_;
}
pub unsafe fn l_Lean_Compiler_LCNF_cse___boxed(
    mut v_phase_3971_: *mut LeanObject,
    mut v_shouldElimFunDecls_3972_: *mut LeanObject,
    mut v_occurrence_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_3974_: u8 = 0;
    let mut v_shouldElimFunDecls_boxed_3975_: u8 = 0;
    let mut v_res_3976_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_3974_ = (lean_unbox(v_phase_3971_) as u8);
    v_shouldElimFunDecls_boxed_3975_ = (lean_unbox(v_shouldElimFunDecls_3972_) as u8);
    v_res_3976_ = l_Lean_Compiler_LCNF_cse(
        v_phase_boxed_3974_,
        v_shouldElimFunDecls_boxed_3975_,
        v_occurrence_3973_,
    );
    return v_res_3976_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: u8 = 0;
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    v___x_4047_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_;
    v___x_4048_ = 1;
    v___x_4049_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_;
    v___x_4050_ = l_Lean_registerTraceClass(v___x_4047_, v___x_4048_, v___x_4049_);
    return v___x_4050_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2____boxed(
    mut v_a_4051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4052_: *mut LeanObject = core::ptr::null_mut();
    v_res_4052_ = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
    return v_res_4052_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_CSE(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NeverExtractAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse =
        _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse();
    lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMPureFalse);
    res = l___private_Lean_Compiler_LCNF_CSE_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CSE_527537415____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_CSE(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_CSE(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_NeverExtractAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CSE(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_CSE(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_CSE(builtin);
}

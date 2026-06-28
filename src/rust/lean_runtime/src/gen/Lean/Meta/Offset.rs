// Lean compiler output
// Module: Lean.Meta.Offset
// Imports: Lean.Data.LBool Lean.Meta.Basic Lean.Meta.NatInstTesters Lean.Util.SafeExponentiation
use crate::r#gen::Init::Control::Option::{
    l_OptionT_bind, l_OptionT_instMonad___redArg___lam__1, l_OptionT_instMonad___redArg___lam__3,
    l_OptionT_instMonad___redArg___lam__6, l_OptionT_instMonad___redArg___lam__9,
    l_OptionT_instMonad___redArg___lam__11, l_OptionT_lift, l_OptionT_lift___redArg___lam__0,
    l_OptionT_pure,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::LBool::{
    initialize_Lean_Data_LBool, l_Bool_toLBool, runtime_initialize_Lean_Data_LBool,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_getAppFn,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_isMVar, l_Lean_Nat_mkInstAdd,
    l_Lean_Nat_mkInstHAdd, l_Lean_mkConst, l_Lean_mkNatAdd, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instMonadMCtxMetaM,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_isExprDefEqAux___boxed, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_Structural_isInstAddNat___redArg,
    l_Lean_Meta_Structural_isInstDivNat___redArg, l_Lean_Meta_Structural_isInstHAddNat___redArg,
    l_Lean_Meta_Structural_isInstHDivNat___redArg, l_Lean_Meta_Structural_isInstHModNat___redArg,
    l_Lean_Meta_Structural_isInstHMulNat___redArg, l_Lean_Meta_Structural_isInstHPowNat___redArg,
    l_Lean_Meta_Structural_isInstHSubNat___redArg, l_Lean_Meta_Structural_isInstModNat___redArg,
    l_Lean_Meta_Structural_isInstMulNat___redArg, l_Lean_Meta_Structural_isInstNatPowNat___redArg,
    l_Lean_Meta_Structural_isInstOfNatNat___redArg, l_Lean_Meta_Structural_isInstPowNat___redArg,
    l_Lean_Meta_Structural_isInstSubNat___redArg, runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0, l_Lean_instantiateMVars___redArg,
};
use crate::r#gen::Lean::Util::SafeExponentiation::{
    initialize_Lean_Util_SafeExponentiation, l_Lean_checkExponent,
    runtime_initialize_Lean_Util_SafeExponentiation,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mod,
    lean_nat_mul, lean_nat_pow, lean_nat_sub, lean_string_dec_eq,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_is_expr_def_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_OptionT_lift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6_value
) as *mut LeanObject;
pub static l_Lean_Meta_evalNat___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_evalNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_evalNat___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [122, 101, 114, 111, 0],
};
static mut l_Lean_Meta_evalNat___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_evalNat___closed__2_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Meta_evalNat___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 117, 99, 99, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__0_value
        ) as *mut LeanObject,
        16112798088292836701 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [112, 111, 119, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value
        ) as *mut LeanObject,
        12575144887947903131 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 111, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value
        ) as *mut LeanObject,
        12949559390826956276 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [100, 105, 118, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value
        ) as *mut LeanObject,
        6783622666262037315 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 117, 108, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value
        ) as *mut LeanObject,
        14305945245784925820 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 117, 98, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value
        ) as *mut LeanObject,
        14164270359643785481 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 100, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value
        ) as *mut LeanObject,
        17073733886952259026 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [79, 102, 78, 97, 116, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__14_value
        ) as *mut LeanObject,
        17636616155771105671 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__15_value
        ) as *mut LeanObject,
        15578568367168711682 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [78, 97, 116, 80, 111, 119, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__17_value
        ) as *mut LeanObject,
        2318246515261832228 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value
        ) as *mut LeanObject,
        18094592700266237200 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [77, 111, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__19_value
        ) as *mut LeanObject,
        153820862758296973 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__4_value
        ) as *mut LeanObject,
        212468567679798298 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [68, 105, 118, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__21_value
        ) as *mut LeanObject,
        6322760582423967641 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__6_value
        ) as *mut LeanObject,
        5832142760602783257 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [77, 117, 108, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__23_value
        ) as *mut LeanObject,
        4707481103260653979 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__8_value
        ) as *mut LeanObject,
        11383192766313517692 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 117, 98, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__25_value
        ) as *mut LeanObject,
        17777553589755654859 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__10_value
        ) as *mut LeanObject,
        13937624386390108825 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 100, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__27_value
        ) as *mut LeanObject,
        17313347264508353403 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__12_value
        ) as *mut LeanObject,
        6683391611519377970 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [80, 111, 119, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__29_value
        ) as *mut LeanObject,
        2611371707704000749 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__2_value
        ) as *mut LeanObject,
        3425896418796058509 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 80, 111, 119, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 80, 111, 119, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__31_value
        ) as *mut LeanObject,
        12847922472053947547 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__32_value
        ) as *mut LeanObject,
        10422657989269798688 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 77, 111, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 77, 111, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__34_value
        ) as *mut LeanObject,
        13744984671752750173 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__35_value
        ) as *mut LeanObject,
        9682224670061807480 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 68, 105, 118, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 68, 105, 118, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__37_value
        ) as *mut LeanObject,
        11858238400308895562 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__38_value
        ) as *mut LeanObject,
        6100819061652633370 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 77, 117, 108, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 77, 117, 108, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__40_value
        ) as *mut LeanObject,
        2929883540436775422 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__41_value
        ) as *mut LeanObject,
        1611444129324655608 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 83, 117, 98, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 83, 117, 98, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__43_value
        ) as *mut LeanObject,
        16856108565602861689 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__44_value
        ) as *mut LeanObject,
        4187025665268973031 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 65, 100, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 65, 100, 100, 0],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46_value)
        as *mut LeanObject;
static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__46_value
        ) as *mut LeanObject,
        10393083817453678557 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__47_value
        ) as *mut LeanObject,
        10680564408669940870 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48_value)
        as *mut LeanObject;
pub static l_Lean_Meta_isDefEqOffset___closed__0_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_evalNat___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_isDefEqOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isDefEqOffset___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_isDefEqOffset___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_isDefEqOffset___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_isDefEqOffset___closed__2_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_isDefEqOffset___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Meta_isDefEqOffset___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isDefEqOffset___closed__2_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    v___x_1839_ = l_instMonadEIO(lean_box(0));
    return v___x_1839_;
}
pub unsafe fn _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    v___x_1840_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0_once), _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0);
    v___x_1841_ = l_StateRefT_x27_instMonad___redArg(v___x_1840_);
    return v___x_1841_;
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(
    mut v_e_1848_: *mut LeanObject,
    mut v_k_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v_toFunctor_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v___f_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyMCtx_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384__overap_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1918_: u8 = 0;
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_a_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1939_: u8 = 0;
    let mut v_reuseFailAlloc_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_unused_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut v_unused_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1855_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once), _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
                v_toApplicative_1856_ = lean_ctor_get(v___x_1855_, 0);
                v_toFunctor_1857_ = lean_ctor_get(v_toApplicative_1856_, 0);
                v_toSeq_1858_ = lean_ctor_get(v_toApplicative_1856_, 2);
                v_toSeqLeft_1859_ = lean_ctor_get(v_toApplicative_1856_, 3);
                v_toSeqRight_1860_ = lean_ctor_get(v_toApplicative_1856_, 4);
                v___f_1861_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
                v___f_1862_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
                lean_inc_ref_n(v_toFunctor_1857_, 2);
                v___f_1863_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1863_, 0, v_toFunctor_1857_);
                v___f_1864_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1864_, 0, v_toFunctor_1857_);
                v___x_1865_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1865_, 0, v___f_1863_);
                lean_ctor_set(v___x_1865_, 1, v___f_1864_);
                lean_inc(v_toSeqRight_1860_);
                v___f_1866_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1866_, 0, v_toSeqRight_1860_);
                lean_inc(v_toSeqLeft_1859_);
                v___f_1867_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1867_, 0, v_toSeqLeft_1859_);
                lean_inc(v_toSeq_1858_);
                v___f_1868_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1868_, 0, v_toSeq_1858_);
                v___x_1869_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1869_, 0, v___x_1865_);
                lean_ctor_set(v___x_1869_, 1, v___f_1861_);
                lean_ctor_set(v___x_1869_, 2, v___f_1868_);
                lean_ctor_set(v___x_1869_, 3, v___f_1867_);
                lean_ctor_set(v___x_1869_, 4, v___f_1866_);
                v___x_1870_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1870_, 0, v___x_1869_);
                lean_ctor_set(v___x_1870_, 1, v___f_1862_);
                v___x_1871_ = l_StateRefT_x27_instMonad___redArg(v___x_1870_);
                v_toApplicative_1872_ = lean_ctor_get(v___x_1871_, 0);
                v_isSharedCheck_1944_ = (!lean_is_exclusive(v___x_1871_)) as u8;
                if v_isSharedCheck_1944_ == 0 {
                    v_unused_1945_ = lean_ctor_get(v___x_1871_, 1);
                    lean_dec(v_unused_1945_);
                    v___x_1874_ = v___x_1871_;
                    v_isShared_1875_ = v_isSharedCheck_1944_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1872_);
                    lean_dec(v___x_1871_);
                    v___x_1874_ = lean_box(0);
                    v_isShared_1875_ = v_isSharedCheck_1944_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1876_ = lean_ctor_get(v_toApplicative_1872_, 0);
                v_toSeq_1877_ = lean_ctor_get(v_toApplicative_1872_, 2);
                v_toSeqLeft_1878_ = lean_ctor_get(v_toApplicative_1872_, 3);
                v_toSeqRight_1879_ = lean_ctor_get(v_toApplicative_1872_, 4);
                v_isSharedCheck_1942_ = (!lean_is_exclusive(v_toApplicative_1872_)) as u8;
                if v_isSharedCheck_1942_ == 0 {
                    v_unused_1943_ = lean_ctor_get(v_toApplicative_1872_, 1);
                    lean_dec(v_unused_1943_);
                    v___x_1881_ = v_toApplicative_1872_;
                    v_isShared_1882_ = v_isSharedCheck_1942_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1879_);
                    lean_inc(v_toSeqLeft_1878_);
                    lean_inc(v_toSeq_1877_);
                    lean_inc(v_toFunctor_1876_);
                    lean_dec(v_toApplicative_1872_);
                    v___x_1881_ = lean_box(0);
                    v_isShared_1882_ = v_isSharedCheck_1942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1883_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
                v___f_1884_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
                lean_inc_ref(v_toFunctor_1876_);
                v___f_1885_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1885_, 0, v_toFunctor_1876_);
                v___f_1886_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1886_, 0, v_toFunctor_1876_);
                v___x_1887_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1887_, 0, v___f_1885_);
                lean_ctor_set(v___x_1887_, 1, v___f_1886_);
                v___f_1888_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1888_, 0, v_toSeqRight_1879_);
                v___f_1889_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1889_, 0, v_toSeqLeft_1878_);
                v___f_1890_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1890_, 0, v_toSeq_1877_);
                if v_isShared_1882_ == 0 {
                    lean_ctor_set(v___x_1881_, 4, v___f_1888_);
                    lean_ctor_set(v___x_1881_, 3, v___f_1889_);
                    lean_ctor_set(v___x_1881_, 2, v___f_1890_);
                    lean_ctor_set(v___x_1881_, 1, v___f_1883_);
                    lean_ctor_set(v___x_1881_, 0, v___x_1887_);
                    v___x_1892_ = v___x_1881_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1887_);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___f_1883_);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 2, v___f_1890_);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 3, v___f_1889_);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 4, v___f_1888_);
                    v___x_1892_ = v_reuseFailAlloc_1941_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1875_ == 0 {
                    lean_ctor_set(v___x_1874_, 1, v___f_1884_);
                    lean_ctor_set(v___x_1874_, 0, v___x_1892_);
                    v___x_1894_ = v___x_1874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1892_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___f_1884_);
                    v___x_1894_ = v_reuseFailAlloc_1940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref_n(v___x_1894_, 7);
                v___f_1895_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_1895_, 0, v___x_1894_);
                v___f_1896_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_1896_, 0, v___x_1894_);
                v___f_1897_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_1897_, 0, v___x_1894_);
                v___f_1898_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_1898_, 0, v___x_1894_);
                v___f_1899_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_1899_, 0, v___x_1894_);
                v___x_1900_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1900_, 0, v___f_1895_);
                lean_ctor_set(v___x_1900_, 1, v___f_1896_);
                v___x_1901_ = lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___x_1901_, 0, lean_box(0));
                lean_closure_set(v___x_1901_, 1, v___x_1894_);
                v___x_1902_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1902_, 0, v___x_1900_);
                lean_ctor_set(v___x_1902_, 1, v___x_1901_);
                lean_ctor_set(v___x_1902_, 2, v___f_1897_);
                lean_ctor_set(v___x_1902_, 3, v___f_1898_);
                lean_ctor_set(v___x_1902_, 4, v___f_1899_);
                v___x_1903_ = lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
                lean_closure_set(v___x_1903_, 0, lean_box(0));
                lean_closure_set(v___x_1903_, 1, v___x_1894_);
                v___x_1904_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1904_, 0, v___x_1902_);
                lean_ctor_set(v___x_1904_, 1, v___x_1903_);
                v___x_1905_ = l_Lean_Meta_instMonadMCtxMetaM;
                v_getMCtx_1906_ = lean_ctor_get(v___x_1905_, 0);
                v_modifyMCtx_1907_ = lean_ctor_get(v___x_1905_, 1);
                v___x_1908_ = lean_alloc_closure(l_OptionT_lift as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___x_1908_, 0, lean_box(0));
                lean_closure_set(v___x_1908_, 1, v___x_1894_);
                lean_inc(v_modifyMCtx_1907_);
                v___f_1909_ = lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1909_, 0, v_modifyMCtx_1907_);
                lean_closure_set(v___f_1909_, 1, v___x_1908_);
                v___f_1910_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
                lean_inc(v_getMCtx_1906_);
                v___x_1911_ = lean_alloc_closure(
                    l_Lean_Meta_instMonadMetaM___lam__1___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_1911_, 0, lean_box(0));
                lean_closure_set(v___x_1911_, 1, lean_box(0));
                lean_closure_set(v___x_1911_, 2, v_getMCtx_1906_);
                lean_closure_set(v___x_1911_, 3, v___f_1910_);
                v___x_1912_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1912_, 0, v___x_1911_);
                lean_ctor_set(v___x_1912_, 1, v___f_1909_);
                v___x_384__overap_1913_ =
                    l_Lean_instantiateMVars___redArg(v___x_1904_, v___x_1912_, v_e_1848_);
                lean_inc(v_a_1853_);
                lean_inc_ref(v_a_1852_);
                lean_inc(v_a_1851_);
                lean_inc_ref(v_a_1850_);
                v___x_1914_ = lean_apply_5(
                    v___x_384__overap_1913_,
                    v_a_1850_,
                    v_a_1851_,
                    v_a_1852_,
                    v_a_1853_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1914_) == 0 {
                    v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
                    v_isSharedCheck_1931_ = (!lean_is_exclusive(v___x_1914_)) as u8;
                    if v_isSharedCheck_1931_ == 0 {
                        v___x_1917_ = v___x_1914_;
                        v_isShared_1918_ = v_isSharedCheck_1931_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1915_);
                        lean_dec(v___x_1914_);
                        v___x_1917_ = lean_box(0);
                        v_isShared_1918_ = v_isSharedCheck_1931_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_k_1849_);
                    v_a_1932_ = lean_ctor_get(v___x_1914_, 0);
                    v_isSharedCheck_1939_ = (!lean_is_exclusive(v___x_1914_)) as u8;
                    if v_isSharedCheck_1939_ == 0 {
                        v___x_1934_ = v___x_1914_;
                        v_isShared_1935_ = v_isSharedCheck_1939_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1932_);
                        lean_dec(v___x_1914_);
                        v___x_1934_ = lean_box(0);
                        v_isShared_1935_ = v_isSharedCheck_1939_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_1915_) == 0 {
                    lean_dec_ref(v_k_1849_);
                    v___x_1919_ = lean_box(0);
                    if v_isShared_1918_ == 0 {
                        lean_ctor_set(v___x_1917_, 0, v___x_1919_);
                        v___x_1921_ = v___x_1917_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
                        v___x_1921_ = v_reuseFailAlloc_1922_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_val_1923_ = lean_ctor_get(v_a_1915_, 0);
                    lean_inc(v_val_1923_);
                    lean_dec_ref_known(v_a_1915_, 1);
                    v___x_1924_ = l_Lean_Expr_getAppFn(v_val_1923_);
                    v___x_1925_ = l_Lean_Expr_isMVar(v___x_1924_);
                    lean_dec_ref(v___x_1924_);
                    if v___x_1925_ == 0 {
                        lean_del_object(v___x_1917_);
                        lean_inc(v_a_1853_);
                        lean_inc_ref(v_a_1852_);
                        lean_inc(v_a_1851_);
                        lean_inc_ref(v_a_1850_);
                        v___x_1926_ = lean_apply_6(
                            v_k_1849_,
                            v_val_1923_,
                            v_a_1850_,
                            v_a_1851_,
                            v_a_1852_,
                            v_a_1853_,
                            lean_box(0),
                        );
                        return v___x_1926_;
                    } else {
                        lean_dec(v_val_1923_);
                        lean_dec_ref(v_k_1849_);
                        v___x_1927_ = lean_box(0);
                        if v_isShared_1918_ == 0 {
                            lean_ctor_set(v___x_1917_, 0, v___x_1927_);
                            v___x_1929_ = v___x_1917_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
                            v___x_1929_ = v_reuseFailAlloc_1930_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_1921_;
            }
            7 => {
                return v___x_1929_;
            }
            8 => {
                if v_isShared_1935_ == 0 {
                    v___x_1937_ = v___x_1934_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
                    v___x_1937_ = v_reuseFailAlloc_1938_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1937_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___boxed(
    mut v_e_1946_: *mut LeanObject,
    mut v_k_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1953_: *mut LeanObject = core::ptr::null_mut();
    v_res_1953_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(
        v_e_1946_, v_k_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_,
    );
    lean_dec(v_a_1951_);
    lean_dec_ref(v_a_1950_);
    lean_dec(v_a_1949_);
    lean_dec_ref(v_a_1948_);
    return v_res_1953_;
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(
    mut v_00_u03b1_1954_: *mut LeanObject,
    mut v_e_1955_: *mut LeanObject,
    mut v_k_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v_toFunctor_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1989_: u8 = 0;
    let mut v___f_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyMCtx_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490__overap_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: u8 = 0;
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_a_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_reuseFailAlloc_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_unused_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2051_: u8 = 0;
    let mut v_unused_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1962_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1_once), _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
                v_toApplicative_1963_ = lean_ctor_get(v___x_1962_, 0);
                v_toFunctor_1964_ = lean_ctor_get(v_toApplicative_1963_, 0);
                v_toSeq_1965_ = lean_ctor_get(v_toApplicative_1963_, 2);
                v_toSeqLeft_1966_ = lean_ctor_get(v_toApplicative_1963_, 3);
                v_toSeqRight_1967_ = lean_ctor_get(v_toApplicative_1963_, 4);
                v___f_1968_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
                v___f_1969_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
                lean_inc_ref_n(v_toFunctor_1964_, 2);
                v___f_1970_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1970_, 0, v_toFunctor_1964_);
                v___f_1971_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1971_, 0, v_toFunctor_1964_);
                v___x_1972_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1972_, 0, v___f_1970_);
                lean_ctor_set(v___x_1972_, 1, v___f_1971_);
                lean_inc(v_toSeqRight_1967_);
                v___f_1973_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1973_, 0, v_toSeqRight_1967_);
                lean_inc(v_toSeqLeft_1966_);
                v___f_1974_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1974_, 0, v_toSeqLeft_1966_);
                lean_inc(v_toSeq_1965_);
                v___f_1975_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1975_, 0, v_toSeq_1965_);
                v___x_1976_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1976_, 0, v___x_1972_);
                lean_ctor_set(v___x_1976_, 1, v___f_1968_);
                lean_ctor_set(v___x_1976_, 2, v___f_1975_);
                lean_ctor_set(v___x_1976_, 3, v___f_1974_);
                lean_ctor_set(v___x_1976_, 4, v___f_1973_);
                v___x_1977_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1977_, 0, v___x_1976_);
                lean_ctor_set(v___x_1977_, 1, v___f_1969_);
                v___x_1978_ = l_StateRefT_x27_instMonad___redArg(v___x_1977_);
                v_toApplicative_1979_ = lean_ctor_get(v___x_1978_, 0);
                v_isSharedCheck_2051_ = (!lean_is_exclusive(v___x_1978_)) as u8;
                if v_isSharedCheck_2051_ == 0 {
                    v_unused_2052_ = lean_ctor_get(v___x_1978_, 1);
                    lean_dec(v_unused_2052_);
                    v___x_1981_ = v___x_1978_;
                    v_isShared_1982_ = v_isSharedCheck_2051_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1979_);
                    lean_dec(v___x_1978_);
                    v___x_1981_ = lean_box(0);
                    v_isShared_1982_ = v_isSharedCheck_2051_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1983_ = lean_ctor_get(v_toApplicative_1979_, 0);
                v_toSeq_1984_ = lean_ctor_get(v_toApplicative_1979_, 2);
                v_toSeqLeft_1985_ = lean_ctor_get(v_toApplicative_1979_, 3);
                v_toSeqRight_1986_ = lean_ctor_get(v_toApplicative_1979_, 4);
                v_isSharedCheck_2049_ = (!lean_is_exclusive(v_toApplicative_1979_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v_unused_2050_ = lean_ctor_get(v_toApplicative_1979_, 1);
                    lean_dec(v_unused_2050_);
                    v___x_1988_ = v_toApplicative_1979_;
                    v_isShared_1989_ = v_isSharedCheck_2049_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1986_);
                    lean_inc(v_toSeqLeft_1985_);
                    lean_inc(v_toSeq_1984_);
                    lean_inc(v_toFunctor_1983_);
                    lean_dec(v_toApplicative_1979_);
                    v___x_1988_ = lean_box(0);
                    v_isShared_1989_ = v_isSharedCheck_2049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1990_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
                v___f_1991_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
                lean_inc_ref(v_toFunctor_1983_);
                v___f_1992_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1992_, 0, v_toFunctor_1983_);
                v___f_1993_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1993_, 0, v_toFunctor_1983_);
                v___x_1994_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1994_, 0, v___f_1992_);
                lean_ctor_set(v___x_1994_, 1, v___f_1993_);
                v___f_1995_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1995_, 0, v_toSeqRight_1986_);
                v___f_1996_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1996_, 0, v_toSeqLeft_1985_);
                v___f_1997_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1997_, 0, v_toSeq_1984_);
                if v_isShared_1989_ == 0 {
                    lean_ctor_set(v___x_1988_, 4, v___f_1995_);
                    lean_ctor_set(v___x_1988_, 3, v___f_1996_);
                    lean_ctor_set(v___x_1988_, 2, v___f_1997_);
                    lean_ctor_set(v___x_1988_, 1, v___f_1990_);
                    lean_ctor_set(v___x_1988_, 0, v___x_1994_);
                    v___x_1999_ = v___x_1988_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_1994_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___f_1990_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 2, v___f_1997_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 3, v___f_1996_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 4, v___f_1995_);
                    v___x_1999_ = v_reuseFailAlloc_2048_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1982_ == 0 {
                    lean_ctor_set(v___x_1981_, 1, v___f_1991_);
                    lean_ctor_set(v___x_1981_, 0, v___x_1999_);
                    v___x_2001_ = v___x_1981_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_1999_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___f_1991_);
                    v___x_2001_ = v_reuseFailAlloc_2047_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref_n(v___x_2001_, 7);
                v___f_2002_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_2002_, 0, v___x_2001_);
                v___f_2003_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_2003_, 0, v___x_2001_);
                v___f_2004_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_2004_, 0, v___x_2001_);
                v___f_2005_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_2005_, 0, v___x_2001_);
                v___f_2006_ = lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_2006_, 0, v___x_2001_);
                v___x_2007_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2007_, 0, v___f_2002_);
                lean_ctor_set(v___x_2007_, 1, v___f_2003_);
                v___x_2008_ = lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___x_2008_, 0, lean_box(0));
                lean_closure_set(v___x_2008_, 1, v___x_2001_);
                v___x_2009_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2009_, 0, v___x_2007_);
                lean_ctor_set(v___x_2009_, 1, v___x_2008_);
                lean_ctor_set(v___x_2009_, 2, v___f_2004_);
                lean_ctor_set(v___x_2009_, 3, v___f_2005_);
                lean_ctor_set(v___x_2009_, 4, v___f_2006_);
                v___x_2010_ = lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
                lean_closure_set(v___x_2010_, 0, lean_box(0));
                lean_closure_set(v___x_2010_, 1, v___x_2001_);
                v___x_2011_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2011_, 0, v___x_2009_);
                lean_ctor_set(v___x_2011_, 1, v___x_2010_);
                v___x_2012_ = l_Lean_Meta_instMonadMCtxMetaM;
                v_getMCtx_2013_ = lean_ctor_get(v___x_2012_, 0);
                v_modifyMCtx_2014_ = lean_ctor_get(v___x_2012_, 1);
                v___x_2015_ = lean_alloc_closure(l_OptionT_lift as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___x_2015_, 0, lean_box(0));
                lean_closure_set(v___x_2015_, 1, v___x_2001_);
                lean_inc(v_modifyMCtx_2014_);
                v___f_2016_ = lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2016_, 0, v_modifyMCtx_2014_);
                lean_closure_set(v___f_2016_, 1, v___x_2015_);
                v___f_2017_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
                lean_inc(v_getMCtx_2013_);
                v___x_2018_ = lean_alloc_closure(
                    l_Lean_Meta_instMonadMetaM___lam__1___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_2018_, 0, lean_box(0));
                lean_closure_set(v___x_2018_, 1, lean_box(0));
                lean_closure_set(v___x_2018_, 2, v_getMCtx_2013_);
                lean_closure_set(v___x_2018_, 3, v___f_2017_);
                v___x_2019_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2019_, 0, v___x_2018_);
                lean_ctor_set(v___x_2019_, 1, v___f_2016_);
                v___x_490__overap_2020_ =
                    l_Lean_instantiateMVars___redArg(v___x_2011_, v___x_2019_, v_e_1955_);
                lean_inc(v_a_1960_);
                lean_inc_ref(v_a_1959_);
                lean_inc(v_a_1958_);
                lean_inc_ref(v_a_1957_);
                v___x_2021_ = lean_apply_5(
                    v___x_490__overap_2020_,
                    v_a_1957_,
                    v_a_1958_,
                    v_a_1959_,
                    v_a_1960_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2021_) == 0 {
                    v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2038_ = (!lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v___x_2024_ = v___x_2021_;
                        v_isShared_2025_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2022_);
                        lean_dec(v___x_2021_);
                        v___x_2024_ = lean_box(0);
                        v_isShared_2025_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_k_1956_);
                    v_a_2039_ = lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2046_ = (!lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2041_ = v___x_2021_;
                        v_isShared_2042_ = v_isSharedCheck_2046_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2039_);
                        lean_dec(v___x_2021_);
                        v___x_2041_ = lean_box(0);
                        v_isShared_2042_ = v_isSharedCheck_2046_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_2022_) == 0 {
                    lean_dec_ref(v_k_1956_);
                    v___x_2026_ = lean_box(0);
                    if v_isShared_2025_ == 0 {
                        lean_ctor_set(v___x_2024_, 0, v___x_2026_);
                        v___x_2028_ = v___x_2024_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                        v___x_2028_ = v_reuseFailAlloc_2029_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_val_2030_ = lean_ctor_get(v_a_2022_, 0);
                    lean_inc(v_val_2030_);
                    lean_dec_ref_known(v_a_2022_, 1);
                    v___x_2031_ = l_Lean_Expr_getAppFn(v_val_2030_);
                    v___x_2032_ = l_Lean_Expr_isMVar(v___x_2031_);
                    lean_dec_ref(v___x_2031_);
                    if v___x_2032_ == 0 {
                        lean_del_object(v___x_2024_);
                        lean_inc(v_a_1960_);
                        lean_inc_ref(v_a_1959_);
                        lean_inc(v_a_1958_);
                        lean_inc_ref(v_a_1957_);
                        v___x_2033_ = lean_apply_6(
                            v_k_1956_,
                            v_val_2030_,
                            v_a_1957_,
                            v_a_1958_,
                            v_a_1959_,
                            v_a_1960_,
                            lean_box(0),
                        );
                        return v___x_2033_;
                    } else {
                        lean_dec(v_val_2030_);
                        lean_dec_ref(v_k_1956_);
                        v___x_2034_ = lean_box(0);
                        if v_isShared_2025_ == 0 {
                            lean_ctor_set(v___x_2024_, 0, v___x_2034_);
                            v___x_2036_ = v___x_2024_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
                            v___x_2036_ = v_reuseFailAlloc_2037_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_2028_;
            }
            7 => {
                return v___x_2036_;
            }
            8 => {
                if v_isShared_2042_ == 0 {
                    v___x_2044_ = v___x_2041_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
                    v___x_2044_ = v_reuseFailAlloc_2045_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___boxed(
    mut v_00_u03b1_2053_: *mut LeanObject,
    mut v_e_2054_: *mut LeanObject,
    mut v_k_2055_: *mut LeanObject,
    mut v_a_2056_: *mut LeanObject,
    mut v_a_2057_: *mut LeanObject,
    mut v_a_2058_: *mut LeanObject,
    mut v_a_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2061_: *mut LeanObject = core::ptr::null_mut();
    v_res_2061_ = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(
        v_00_u03b1_2053_,
        v_e_2054_,
        v_k_2055_,
        v_a_2056_,
        v_a_2057_,
        v_a_2058_,
        v_a_2059_,
    );
    lean_dec(v_a_2059_);
    lean_dec_ref(v_a_2058_);
    lean_dec(v_a_2057_);
    lean_dec_ref(v_a_2056_);
    return v_res_2061_;
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(
    mut v_e_2157_: *mut LeanObject,
    mut v_a_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
    mut v_a_2160_: *mut LeanObject,
    mut v_a_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: u8 = 0;
    let mut v_arg_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v___x_2179_: u8 = 0;
    let mut v_arg_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: u8 = 0;
    let mut v_arg_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v_val_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v_unused_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v_a_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2276_: u8 = 0;
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v_val_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2301_: u8 = 0;
    let mut v_isSharedCheck_2302_: u8 = 0;
    let mut v_unused_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut v_a_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2330_: u8 = 0;
    let mut v_val_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v_unused_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2345_: u8 = 0;
    let mut v_a_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2353_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2371_: u8 = 0;
    let mut v_val_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut v_isSharedCheck_2384_: u8 = 0;
    let mut v_unused_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v_val_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2416_: u8 = 0;
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2424_: u8 = 0;
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_unused_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_a_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2447_: u8 = 0;
    let mut v_a_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2451_: u8 = 0;
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2455_: u8 = 0;
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut v_a_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2493_: u8 = 0;
    let mut v_val_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2505_: u8 = 0;
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut v_unused_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut v_a_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2522_: u8 = 0;
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v_val_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_isSharedCheck_2547_: u8 = 0;
    let mut v_unused_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2549_: u8 = 0;
    let mut v_a_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v_val_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_unused_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_a_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2598_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2616_: u8 = 0;
    let mut v_val_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2628_: u8 = 0;
    let mut v_isSharedCheck_2629_: u8 = 0;
    let mut v_unused_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut v_a_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2644_: u8 = 0;
    let mut v___x_2645_: u8 = 0;
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_val_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2661_: u8 = 0;
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut v_isSharedCheck_2670_: u8 = 0;
    let mut v_unused_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_a_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2685_: u8 = 0;
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_a_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v___x_2706_: u8 = 0;
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2712_: u8 = 0;
    let mut v_a_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2716_: u8 = 0;
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v_val_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut v_unused_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v_val_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_isSharedCheck_2763_: u8 = 0;
    let mut v_unused_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2772_: u8 = 0;
    let mut v_val_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut v_unused_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v_val_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2798_: u8 = 0;
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_unused_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v_val_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut v_unused_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v_val_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut v_unused_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_a_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2163_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2157_, v_a_2159_);
                if lean_obj_tag(v___x_2163_) == 0 {
                    v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
                    v_isSharedCheck_2852_ = (!lean_is_exclusive(v___x_2163_)) as u8;
                    if v_isSharedCheck_2852_ == 0 {
                        v___x_2166_ = v___x_2163_;
                        v_isShared_2167_ = v_isSharedCheck_2852_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2164_);
                        lean_dec(v___x_2163_);
                        v___x_2166_ = lean_box(0);
                        v_isShared_2167_ = v_isSharedCheck_2852_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2853_ = lean_ctor_get(v___x_2163_, 0);
                    v_isSharedCheck_2860_ = (!lean_is_exclusive(v___x_2163_)) as u8;
                    if v_isSharedCheck_2860_ == 0 {
                        v___x_2855_ = v___x_2163_;
                        v_isShared_2856_ = v_isSharedCheck_2860_;
                        state = 124;
                        continue;
                    } else {
                        lean_inc(v_a_2853_);
                        lean_dec(v___x_2163_);
                        v___x_2855_ = lean_box(0);
                        v_isShared_2856_ = v_isSharedCheck_2860_;
                        state = 124;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2173_ = l_Lean_Expr_cleanupAnnotations(v_a_2164_);
                v___x_2174_ = l_Lean_Expr_isApp(v___x_2173_);
                if v___x_2174_ == 0 {
                    lean_dec_ref(v___x_2173_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2175_ = lean_ctor_get(v___x_2173_, 1);
                    lean_inc_ref(v_arg_2175_);
                    v___x_2176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2173_);
                    v___x_2177_ =
                        l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1;
                    v___x_2178_ = l_Lean_Expr_isConstOf(v___x_2176_, v___x_2177_);
                    if v___x_2178_ == 0 {
                        v___x_2179_ = l_Lean_Expr_isApp(v___x_2176_);
                        if v___x_2179_ == 0 {
                            lean_dec_ref(v___x_2176_);
                            lean_dec_ref(v_arg_2175_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2180_ = lean_ctor_get(v___x_2176_, 1);
                            lean_inc_ref(v_arg_2180_);
                            v___x_2181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2176_);
                            v___x_2182_ =
                                l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__3;
                            v___x_2183_ = l_Lean_Expr_isConstOf(v___x_2181_, v___x_2182_);
                            if v___x_2183_ == 0 {
                                v___x_2184_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__5;
                                v___x_2185_ = l_Lean_Expr_isConstOf(v___x_2181_, v___x_2184_);
                                if v___x_2185_ == 0 {
                                    v___x_2186_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__7;
                                    v___x_2187_ = l_Lean_Expr_isConstOf(v___x_2181_, v___x_2186_);
                                    if v___x_2187_ == 0 {
                                        v___x_2188_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__9;
                                        v___x_2189_ =
                                            l_Lean_Expr_isConstOf(v___x_2181_, v___x_2188_);
                                        if v___x_2189_ == 0 {
                                            v___x_2190_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__11;
                                            v___x_2191_ =
                                                l_Lean_Expr_isConstOf(v___x_2181_, v___x_2190_);
                                            if v___x_2191_ == 0 {
                                                v___x_2192_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13;
                                                v___x_2193_ =
                                                    l_Lean_Expr_isConstOf(v___x_2181_, v___x_2192_);
                                                if v___x_2193_ == 0 {
                                                    v___x_2194_ = l_Lean_Expr_isApp(v___x_2181_);
                                                    if v___x_2194_ == 0 {
                                                        lean_dec_ref(v___x_2181_);
                                                        lean_dec_ref(v_arg_2180_);
                                                        lean_dec_ref(v_arg_2175_);
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v_arg_2195_ = lean_ctor_get(v___x_2181_, 1);
                                                        lean_inc_ref(v_arg_2195_);
                                                        v___x_2196_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_2181_,
                                                            );
                                                        v___x_2197_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__16;
                                                        v___x_2198_ = l_Lean_Expr_isConstOf(
                                                            v___x_2196_,
                                                            v___x_2197_,
                                                        );
                                                        if v___x_2198_ == 0 {
                                                            v___x_2199_ =
                                                                l_Lean_Expr_isApp(v___x_2196_);
                                                            if v___x_2199_ == 0 {
                                                                lean_dec_ref(v___x_2196_);
                                                                lean_dec_ref(v_arg_2195_);
                                                                lean_dec_ref(v_arg_2180_);
                                                                lean_dec_ref(v_arg_2175_);
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                v___x_2200_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2196_);
                                                                v___x_2201_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__18;
                                                                v___x_2202_ = l_Lean_Expr_isConstOf(
                                                                    v___x_2200_,
                                                                    v___x_2201_,
                                                                );
                                                                if v___x_2202_ == 0 {
                                                                    v___x_2203_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__20;
                                                                    v___x_2204_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_2200_,
                                                                            v___x_2203_,
                                                                        );
                                                                    if v___x_2204_ == 0 {
                                                                        v___x_2205_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__22;
                                                                        v___x_2206_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_2200_,
                                                                                v___x_2205_,
                                                                            );
                                                                        if v___x_2206_ == 0 {
                                                                            v___x_2207_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__24;
                                                                            v___x_2208_ = l_Lean_Expr_isConstOf(v___x_2200_, v___x_2207_);
                                                                            if v___x_2208_ == 0 {
                                                                                v___x_2209_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__26;
                                                                                v___x_2210_ = l_Lean_Expr_isConstOf(v___x_2200_, v___x_2209_);
                                                                                if v___x_2210_ == 0
                                                                                {
                                                                                    v___x_2211_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28;
                                                                                    v___x_2212_ = l_Lean_Expr_isConstOf(v___x_2200_, v___x_2211_);
                                                                                    if v___x_2212_
                                                                                        == 0
                                                                                    {
                                                                                        v___x_2213_ = l_Lean_Expr_isApp(v___x_2200_);
                                                                                        if v___x_2213_ == 0 {
lean_dec_ref(v___x_2200_);
lean_dec_ref(v_arg_2195_);
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
state = 2; continue;
} else {
v___x_2214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2200_);
v___x_2215_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__30;
v___x_2216_ = l_Lean_Expr_isConstOf(v___x_2214_, v___x_2215_);
if v___x_2216_ == 0 {
v___x_2217_ = l_Lean_Expr_isApp(v___x_2214_);
if v___x_2217_ == 0 {
lean_dec_ref(v___x_2214_);
lean_dec_ref(v_arg_2195_);
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
state = 2; continue;
} else {
v___x_2218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2214_);
v___x_2219_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__33;
v___x_2220_ = l_Lean_Expr_isConstOf(v___x_2218_, v___x_2219_);
if v___x_2220_ == 0 {
v___x_2221_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__36;
v___x_2222_ = l_Lean_Expr_isConstOf(v___x_2218_, v___x_2221_);
if v___x_2222_ == 0 {
v___x_2223_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__39;
v___x_2224_ = l_Lean_Expr_isConstOf(v___x_2218_, v___x_2223_);
if v___x_2224_ == 0 {
v___x_2225_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__42;
v___x_2226_ = l_Lean_Expr_isConstOf(v___x_2218_, v___x_2225_);
if v___x_2226_ == 0 {
v___x_2227_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__45;
v___x_2228_ = l_Lean_Expr_isConstOf(v___x_2218_, v___x_2227_);
if v___x_2228_ == 0 {
v___x_2229_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48;
v___x_2230_ = l_Lean_Expr_isConstOf(v___x_2218_, v___x_2229_);
lean_dec_ref(v___x_2218_);
if v___x_2230_ == 0 {
lean_dec_ref(v_arg_2195_);
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
state = 2; continue;
} else {
lean_del_object(v___x_2166_);
v___x_2231_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_2195_, v_a_2159_);
if lean_obj_tag(v___x_2231_) == 0 {
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2263_ = (!lean_is_exclusive(v___x_2231_)) as u8;
if v_isSharedCheck_2263_ == 0 {
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2263_;
state = 4; continue;
} else {
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2263_;
state = 4; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2264_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2271_ = (!lean_is_exclusive(v___x_2231_)) as u8;
if v_isSharedCheck_2271_ == 0 {
v___x_2266_ = v___x_2231_;
v_isShared_2267_ = v_isSharedCheck_2271_;
state = 10; continue;
} else {
lean_inc(v_a_2264_);
lean_dec(v___x_2231_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
state = 10; continue;
}
}
}
} else {
lean_dec_ref(v___x_2218_);
lean_del_object(v___x_2166_);
v___x_2272_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_2195_, v_a_2159_);
if lean_obj_tag(v___x_2272_) == 0 {
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2304_ = (!lean_is_exclusive(v___x_2272_)) as u8;
if v_isSharedCheck_2304_ == 0 {
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2304_;
state = 12; continue;
} else {
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2304_;
state = 12; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2305_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2312_ = (!lean_is_exclusive(v___x_2272_)) as u8;
if v_isSharedCheck_2312_ == 0 {
v___x_2307_ = v___x_2272_;
v_isShared_2308_ = v_isSharedCheck_2312_;
state = 18; continue;
} else {
lean_inc(v_a_2305_);
lean_dec(v___x_2272_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
state = 18; continue;
}
}
}
} else {
lean_dec_ref(v___x_2218_);
lean_del_object(v___x_2166_);
v___x_2313_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_2195_, v_a_2159_);
if lean_obj_tag(v___x_2313_) == 0 {
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2345_ = (!lean_is_exclusive(v___x_2313_)) as u8;
if v_isSharedCheck_2345_ == 0 {
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2345_;
state = 20; continue;
} else {
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2345_;
state = 20; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2346_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2353_ = (!lean_is_exclusive(v___x_2313_)) as u8;
if v_isSharedCheck_2353_ == 0 {
v___x_2348_ = v___x_2313_;
v_isShared_2349_ = v_isSharedCheck_2353_;
state = 26; continue;
} else {
lean_inc(v_a_2346_);
lean_dec(v___x_2313_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
state = 26; continue;
}
}
}
} else {
lean_dec_ref(v___x_2218_);
lean_del_object(v___x_2166_);
v___x_2354_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_2195_, v_a_2159_);
if lean_obj_tag(v___x_2354_) == 0 {
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2386_ = (!lean_is_exclusive(v___x_2354_)) as u8;
if v_isSharedCheck_2386_ == 0 {
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2386_;
state = 28; continue;
} else {
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2386_;
state = 28; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2387_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2394_ = (!lean_is_exclusive(v___x_2354_)) as u8;
if v_isSharedCheck_2394_ == 0 {
v___x_2389_ = v___x_2354_;
v_isShared_2390_ = v_isSharedCheck_2394_;
state = 34; continue;
} else {
lean_inc(v_a_2387_);
lean_dec(v___x_2354_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
state = 34; continue;
}
}
}
} else {
lean_dec_ref(v___x_2218_);
lean_del_object(v___x_2166_);
v___x_2395_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_2195_, v_a_2159_);
if lean_obj_tag(v___x_2395_) == 0 {
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2427_ = (!lean_is_exclusive(v___x_2395_)) as u8;
if v_isSharedCheck_2427_ == 0 {
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2427_;
state = 36; continue;
} else {
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2427_;
state = 36; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2428_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2435_ = (!lean_is_exclusive(v___x_2395_)) as u8;
if v_isSharedCheck_2435_ == 0 {
v___x_2430_ = v___x_2395_;
v_isShared_2431_ = v_isSharedCheck_2435_;
state = 42; continue;
} else {
lean_inc(v_a_2428_);
lean_dec(v___x_2395_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
state = 42; continue;
}
}
}
} else {
lean_dec_ref(v___x_2218_);
lean_del_object(v___x_2166_);
v___x_2436_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_2195_, v_a_2159_);
if lean_obj_tag(v___x_2436_) == 0 {
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2447_ = (!lean_is_exclusive(v___x_2436_)) as u8;
if v_isSharedCheck_2447_ == 0 {
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2447_;
state = 44; continue;
} else {
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2447_;
state = 44; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2448_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2455_ = (!lean_is_exclusive(v___x_2436_)) as u8;
if v_isSharedCheck_2455_ == 0 {
v___x_2450_ = v___x_2436_;
v_isShared_2451_ = v_isSharedCheck_2455_;
state = 46; continue;
} else {
lean_inc(v_a_2448_);
lean_dec(v___x_2436_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
state = 46; continue;
}
}
}
}
} else {
lean_dec_ref(v___x_2214_);
lean_del_object(v___x_2166_);
v___x_2456_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_arg_2195_, v_a_2159_);
if lean_obj_tag(v___x_2456_) == 0 {
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2467_ = (!lean_is_exclusive(v___x_2456_)) as u8;
if v_isSharedCheck_2467_ == 0 {
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2467_;
state = 48; continue;
} else {
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2467_;
state = 48; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2468_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2475_ = (!lean_is_exclusive(v___x_2456_)) as u8;
if v_isSharedCheck_2475_ == 0 {
v___x_2470_ = v___x_2456_;
v_isShared_2471_ = v_isSharedCheck_2475_;
state = 50; continue;
} else {
lean_inc(v_a_2468_);
lean_dec(v___x_2456_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
state = 50; continue;
}
}
}
}
                                                                                    } else {
                                                                                        lean_dec_ref(v___x_2200_);
                                                                                        lean_del_object(v___x_2166_);
                                                                                        v___x_2476_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_arg_2195_, v_a_2159_);
                                                                                        if lean_obj_tag(v___x_2476_) == 0 {
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2508_ = (!lean_is_exclusive(v___x_2476_)) as u8;
if v_isSharedCheck_2508_ == 0 {
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2508_;
state = 52; continue;
} else {
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2508_;
state = 52; continue;
}
} else {
lean_dec_ref(v_arg_2180_);
lean_dec_ref(v_arg_2175_);
v_a_2509_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2516_ = (!lean_is_exclusive(v___x_2476_)) as u8;
if v_isSharedCheck_2516_ == 0 {
v___x_2511_ = v___x_2476_;
v_isShared_2512_ = v_isSharedCheck_2516_;
state = 58; continue;
} else {
lean_inc(v_a_2509_);
lean_dec(v___x_2476_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
state = 58; continue;
}
}
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v___x_2200_,
                                                                                    );
                                                                                    lean_del_object(
                                                                                        v___x_2166_,
                                                                                    );
                                                                                    v___x_2517_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_arg_2195_, v_a_2159_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_2517_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
                                                                                        v_isSharedCheck_2549_ = (!lean_is_exclusive(v___x_2517_)) as u8;
                                                                                        if v_isSharedCheck_2549_ == 0 {
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2549_;
state = 60; continue;
} else {
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2549_;
state = 60; continue;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v_arg_2180_);
                                                                                        lean_dec_ref(v_arg_2175_);
                                                                                        v_a_2550_ = lean_ctor_get(v___x_2517_, 0);
                                                                                        v_isSharedCheck_2557_ = (!lean_is_exclusive(v___x_2517_)) as u8;
                                                                                        if v_isSharedCheck_2557_ == 0 {
v___x_2552_ = v___x_2517_;
v_isShared_2553_ = v_isSharedCheck_2557_;
state = 66; continue;
} else {
lean_inc(v_a_2550_);
lean_dec(v___x_2517_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
state = 66; continue;
}
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v___x_2200_,
                                                                                );
                                                                                lean_del_object(
                                                                                    v___x_2166_,
                                                                                );
                                                                                v___x_2558_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_arg_2195_, v_a_2159_);
                                                                                if lean_obj_tag(
                                                                                    v___x_2558_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
                                                                                    v_isSharedCheck_2590_ = (!lean_is_exclusive(v___x_2558_)) as u8;
                                                                                    if v_isSharedCheck_2590_ == 0 {
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2590_;
state = 68; continue;
} else {
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2590_;
state = 68; continue;
}
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_2180_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_2175_,
                                                                                    );
                                                                                    v_a_2591_ = lean_ctor_get(v___x_2558_, 0);
                                                                                    v_isSharedCheck_2598_ = (!lean_is_exclusive(v___x_2558_)) as u8;
                                                                                    if v_isSharedCheck_2598_ == 0 {
v___x_2593_ = v___x_2558_;
v_isShared_2594_ = v_isSharedCheck_2598_;
state = 74; continue;
} else {
lean_inc(v_a_2591_);
lean_dec(v___x_2558_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
state = 74; continue;
}
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v___x_2200_,
                                                                            );
                                                                            lean_del_object(
                                                                                v___x_2166_,
                                                                            );
                                                                            v___x_2599_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_arg_2195_, v_a_2159_);
                                                                            if lean_obj_tag(
                                                                                v___x_2599_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_2600_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2599_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_2631_ = (!lean_is_exclusive(v___x_2599_)) as u8;
                                                                                if v_isSharedCheck_2631_ == 0 {
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2631_;
state = 76; continue;
} else {
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2631_;
state = 76; continue;
}
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_2180_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_2175_,
                                                                                );
                                                                                v_a_2632_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2599_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_2639_ = (!lean_is_exclusive(v___x_2599_)) as u8;
                                                                                if v_isSharedCheck_2639_ == 0 {
v___x_2634_ = v___x_2599_;
v_isShared_2635_ = v_isSharedCheck_2639_;
state = 82; continue;
} else {
lean_inc(v_a_2632_);
lean_dec(v___x_2599_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
state = 82; continue;
}
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v___x_2200_);
                                                                        lean_del_object(
                                                                            v___x_2166_,
                                                                        );
                                                                        v___x_2640_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_arg_2195_, v_a_2159_);
                                                                        if lean_obj_tag(v___x_2640_)
                                                                            == 0
                                                                        {
                                                                            v_a_2641_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2640_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_2672_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_2640_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_2672_
                                                                                == 0
                                                                            {
                                                                                v___x_2643_ =
                                                                                    v___x_2640_;
                                                                                v_isShared_2644_ = v_isSharedCheck_2672_;
                                                                                state = 84;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_2641_);
                                                                                lean_dec(
                                                                                    v___x_2640_,
                                                                                );
                                                                                v___x_2643_ =
                                                                                    lean_box(0);
                                                                                v_isShared_2644_ = v_isSharedCheck_2672_;
                                                                                state = 84;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_2180_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2175_,
                                                                            );
                                                                            v_a_2673_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2640_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_2680_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_2640_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_2680_
                                                                                == 0
                                                                            {
                                                                                v___x_2675_ =
                                                                                    v___x_2640_;
                                                                                v_isShared_2676_ = v_isSharedCheck_2680_;
                                                                                state = 90;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_2673_);
                                                                                lean_dec(
                                                                                    v___x_2640_,
                                                                                );
                                                                                v___x_2675_ =
                                                                                    lean_box(0);
                                                                                v_isShared_2676_ = v_isSharedCheck_2680_;
                                                                                state = 90;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_2200_);
                                                                    lean_del_object(v___x_2166_);
                                                                    v___x_2681_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_arg_2195_, v_a_2159_);
                                                                    if lean_obj_tag(v___x_2681_)
                                                                        == 0
                                                                    {
                                                                        v_a_2682_ = lean_ctor_get(
                                                                            v___x_2681_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_2692_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_2681_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_2692_
                                                                            == 0
                                                                        {
                                                                            v___x_2684_ =
                                                                                v___x_2681_;
                                                                            v_isShared_2685_ = v_isSharedCheck_2692_;
                                                                            state = 92;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_2682_);
                                                                            lean_dec(v___x_2681_);
                                                                            v___x_2684_ =
                                                                                lean_box(0);
                                                                            v_isShared_2685_ = v_isSharedCheck_2692_;
                                                                            state = 92;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_2180_);
                                                                        lean_dec_ref(v_arg_2175_);
                                                                        v_a_2693_ = lean_ctor_get(
                                                                            v___x_2681_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_2700_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_2681_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_2700_
                                                                            == 0
                                                                        {
                                                                            v___x_2695_ =
                                                                                v___x_2681_;
                                                                            v_isShared_2696_ = v_isSharedCheck_2700_;
                                                                            state = 94;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_2693_);
                                                                            lean_dec(v___x_2681_);
                                                                            v___x_2695_ =
                                                                                lean_box(0);
                                                                            v_isShared_2696_ = v_isSharedCheck_2700_;
                                                                            state = 94;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref(v___x_2196_);
                                                            lean_dec_ref(v_arg_2195_);
                                                            lean_del_object(v___x_2166_);
                                                            v___x_2701_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_arg_2175_, v_a_2159_);
                                                            if lean_obj_tag(v___x_2701_) == 0 {
                                                                v_a_2702_ =
                                                                    lean_ctor_get(v___x_2701_, 0);
                                                                v_isSharedCheck_2712_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_2701_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2712_ == 0 {
                                                                    v___x_2704_ = v___x_2701_;
                                                                    v_isShared_2705_ =
                                                                        v_isSharedCheck_2712_;
                                                                    state = 96;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_2702_);
                                                                    lean_dec(v___x_2701_);
                                                                    v___x_2704_ = lean_box(0);
                                                                    v_isShared_2705_ =
                                                                        v_isSharedCheck_2712_;
                                                                    state = 96;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_2180_);
                                                                v_a_2713_ =
                                                                    lean_ctor_get(v___x_2701_, 0);
                                                                v_isSharedCheck_2720_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_2701_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2720_ == 0 {
                                                                    v___x_2715_ = v___x_2701_;
                                                                    v_isShared_2716_ =
                                                                        v_isSharedCheck_2720_;
                                                                    state = 98;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_2713_);
                                                                    lean_dec(v___x_2701_);
                                                                    v___x_2715_ = lean_box(0);
                                                                    v_isShared_2716_ =
                                                                        v_isSharedCheck_2720_;
                                                                    state = 98;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_2181_);
                                                    lean_del_object(v___x_2166_);
                                                    v___x_2721_ = l_Lean_Meta_evalNat(
                                                        v_arg_2180_,
                                                        v_a_2158_,
                                                        v_a_2159_,
                                                        v_a_2160_,
                                                        v_a_2161_,
                                                    );
                                                    if lean_obj_tag(v___x_2721_) == 0 {
                                                        v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
                                                        lean_inc(v_a_2722_);
                                                        if lean_obj_tag(v_a_2722_) == 0 {
                                                            lean_dec_ref(v_arg_2175_);
                                                            return v___x_2721_;
                                                        } else {
                                                            lean_dec_ref_known(v___x_2721_, 1);
                                                            v_val_2723_ =
                                                                lean_ctor_get(v_a_2722_, 0);
                                                            lean_inc(v_val_2723_);
                                                            lean_dec_ref_known(v_a_2722_, 1);
                                                            v___x_2724_ = l_Lean_Meta_evalNat(
                                                                v_arg_2175_,
                                                                v_a_2158_,
                                                                v_a_2159_,
                                                                v_a_2160_,
                                                                v_a_2161_,
                                                            );
                                                            if lean_obj_tag(v___x_2724_) == 0 {
                                                                v_a_2725_ =
                                                                    lean_ctor_get(v___x_2724_, 0);
                                                                lean_inc(v_a_2725_);
                                                                if lean_obj_tag(v_a_2725_) == 0 {
                                                                    lean_dec(v_val_2723_);
                                                                    return v___x_2724_;
                                                                } else {
                                                                    v_isSharedCheck_2741_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_2724_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_2741_ == 0 {
                                                                        v_unused_2742_ =
                                                                            lean_ctor_get(
                                                                                v___x_2724_,
                                                                                0,
                                                                            );
                                                                        lean_dec(v_unused_2742_);
                                                                        v___x_2727_ = v___x_2724_;
                                                                        v_isShared_2728_ =
                                                                            v_isSharedCheck_2741_;
                                                                        state = 100;
                                                                        continue;
                                                                    } else {
                                                                        lean_dec(v___x_2724_);
                                                                        v___x_2727_ = lean_box(0);
                                                                        v_isShared_2728_ =
                                                                            v_isSharedCheck_2741_;
                                                                        state = 100;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec(v_val_2723_);
                                                                return v___x_2724_;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_2175_);
                                                        return v___x_2721_;
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2181_);
                                                lean_del_object(v___x_2166_);
                                                v___x_2743_ = l_Lean_Meta_evalNat(
                                                    v_arg_2180_,
                                                    v_a_2158_,
                                                    v_a_2159_,
                                                    v_a_2160_,
                                                    v_a_2161_,
                                                );
                                                if lean_obj_tag(v___x_2743_) == 0 {
                                                    v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
                                                    lean_inc(v_a_2744_);
                                                    if lean_obj_tag(v_a_2744_) == 0 {
                                                        lean_dec_ref(v_arg_2175_);
                                                        return v___x_2743_;
                                                    } else {
                                                        lean_dec_ref_known(v___x_2743_, 1);
                                                        v_val_2745_ = lean_ctor_get(v_a_2744_, 0);
                                                        lean_inc(v_val_2745_);
                                                        lean_dec_ref_known(v_a_2744_, 1);
                                                        v___x_2746_ = l_Lean_Meta_evalNat(
                                                            v_arg_2175_,
                                                            v_a_2158_,
                                                            v_a_2159_,
                                                            v_a_2160_,
                                                            v_a_2161_,
                                                        );
                                                        if lean_obj_tag(v___x_2746_) == 0 {
                                                            v_a_2747_ =
                                                                lean_ctor_get(v___x_2746_, 0);
                                                            lean_inc(v_a_2747_);
                                                            if lean_obj_tag(v_a_2747_) == 0 {
                                                                lean_dec(v_val_2745_);
                                                                return v___x_2746_;
                                                            } else {
                                                                v_isSharedCheck_2763_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_2746_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2763_ == 0 {
                                                                    v_unused_2764_ = lean_ctor_get(
                                                                        v___x_2746_,
                                                                        0,
                                                                    );
                                                                    lean_dec(v_unused_2764_);
                                                                    v___x_2749_ = v___x_2746_;
                                                                    v_isShared_2750_ =
                                                                        v_isSharedCheck_2763_;
                                                                    state = 104;
                                                                    continue;
                                                                } else {
                                                                    lean_dec(v___x_2746_);
                                                                    v___x_2749_ = lean_box(0);
                                                                    v_isShared_2750_ =
                                                                        v_isSharedCheck_2763_;
                                                                    state = 104;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec(v_val_2745_);
                                                            return v___x_2746_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_2175_);
                                                    return v___x_2743_;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2181_);
                                            lean_del_object(v___x_2166_);
                                            v___x_2765_ = l_Lean_Meta_evalNat(
                                                v_arg_2180_,
                                                v_a_2158_,
                                                v_a_2159_,
                                                v_a_2160_,
                                                v_a_2161_,
                                            );
                                            if lean_obj_tag(v___x_2765_) == 0 {
                                                v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
                                                lean_inc(v_a_2766_);
                                                if lean_obj_tag(v_a_2766_) == 0 {
                                                    lean_dec_ref(v_arg_2175_);
                                                    return v___x_2765_;
                                                } else {
                                                    lean_dec_ref_known(v___x_2765_, 1);
                                                    v_val_2767_ = lean_ctor_get(v_a_2766_, 0);
                                                    lean_inc(v_val_2767_);
                                                    lean_dec_ref_known(v_a_2766_, 1);
                                                    v___x_2768_ = l_Lean_Meta_evalNat(
                                                        v_arg_2175_,
                                                        v_a_2158_,
                                                        v_a_2159_,
                                                        v_a_2160_,
                                                        v_a_2161_,
                                                    );
                                                    if lean_obj_tag(v___x_2768_) == 0 {
                                                        v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
                                                        lean_inc(v_a_2769_);
                                                        if lean_obj_tag(v_a_2769_) == 0 {
                                                            lean_dec(v_val_2767_);
                                                            return v___x_2768_;
                                                        } else {
                                                            v_isSharedCheck_2785_ =
                                                                (!lean_is_exclusive(v___x_2768_))
                                                                    as u8;
                                                            if v_isSharedCheck_2785_ == 0 {
                                                                v_unused_2786_ =
                                                                    lean_ctor_get(v___x_2768_, 0);
                                                                lean_dec(v_unused_2786_);
                                                                v___x_2771_ = v___x_2768_;
                                                                v_isShared_2772_ =
                                                                    v_isSharedCheck_2785_;
                                                                state = 108;
                                                                continue;
                                                            } else {
                                                                lean_dec(v___x_2768_);
                                                                v___x_2771_ = lean_box(0);
                                                                v_isShared_2772_ =
                                                                    v_isSharedCheck_2785_;
                                                                state = 108;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_val_2767_);
                                                        return v___x_2768_;
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_2175_);
                                                return v___x_2765_;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_2181_);
                                        lean_del_object(v___x_2166_);
                                        v___x_2787_ = l_Lean_Meta_evalNat(
                                            v_arg_2180_,
                                            v_a_2158_,
                                            v_a_2159_,
                                            v_a_2160_,
                                            v_a_2161_,
                                        );
                                        if lean_obj_tag(v___x_2787_) == 0 {
                                            v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
                                            lean_inc(v_a_2788_);
                                            if lean_obj_tag(v_a_2788_) == 0 {
                                                lean_dec_ref(v_arg_2175_);
                                                return v___x_2787_;
                                            } else {
                                                lean_dec_ref_known(v___x_2787_, 1);
                                                v_val_2789_ = lean_ctor_get(v_a_2788_, 0);
                                                lean_inc(v_val_2789_);
                                                lean_dec_ref_known(v_a_2788_, 1);
                                                v___x_2790_ = l_Lean_Meta_evalNat(
                                                    v_arg_2175_,
                                                    v_a_2158_,
                                                    v_a_2159_,
                                                    v_a_2160_,
                                                    v_a_2161_,
                                                );
                                                if lean_obj_tag(v___x_2790_) == 0 {
                                                    v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
                                                    lean_inc(v_a_2791_);
                                                    if lean_obj_tag(v_a_2791_) == 0 {
                                                        lean_dec(v_val_2789_);
                                                        return v___x_2790_;
                                                    } else {
                                                        v_isSharedCheck_2807_ =
                                                            (!lean_is_exclusive(v___x_2790_)) as u8;
                                                        if v_isSharedCheck_2807_ == 0 {
                                                            v_unused_2808_ =
                                                                lean_ctor_get(v___x_2790_, 0);
                                                            lean_dec(v_unused_2808_);
                                                            v___x_2793_ = v___x_2790_;
                                                            v_isShared_2794_ =
                                                                v_isSharedCheck_2807_;
                                                            state = 112;
                                                            continue;
                                                        } else {
                                                            lean_dec(v___x_2790_);
                                                            v___x_2793_ = lean_box(0);
                                                            v_isShared_2794_ =
                                                                v_isSharedCheck_2807_;
                                                            state = 112;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_val_2789_);
                                                    return v___x_2790_;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_2175_);
                                            return v___x_2787_;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_2181_);
                                    lean_del_object(v___x_2166_);
                                    v___x_2809_ = l_Lean_Meta_evalNat(
                                        v_arg_2180_,
                                        v_a_2158_,
                                        v_a_2159_,
                                        v_a_2160_,
                                        v_a_2161_,
                                    );
                                    if lean_obj_tag(v___x_2809_) == 0 {
                                        v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
                                        lean_inc(v_a_2810_);
                                        if lean_obj_tag(v_a_2810_) == 0 {
                                            lean_dec_ref(v_arg_2175_);
                                            return v___x_2809_;
                                        } else {
                                            lean_dec_ref_known(v___x_2809_, 1);
                                            v_val_2811_ = lean_ctor_get(v_a_2810_, 0);
                                            lean_inc(v_val_2811_);
                                            lean_dec_ref_known(v_a_2810_, 1);
                                            v___x_2812_ = l_Lean_Meta_evalNat(
                                                v_arg_2175_,
                                                v_a_2158_,
                                                v_a_2159_,
                                                v_a_2160_,
                                                v_a_2161_,
                                            );
                                            if lean_obj_tag(v___x_2812_) == 0 {
                                                v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
                                                lean_inc(v_a_2813_);
                                                if lean_obj_tag(v_a_2813_) == 0 {
                                                    lean_dec(v_val_2811_);
                                                    return v___x_2812_;
                                                } else {
                                                    v_isSharedCheck_2829_ =
                                                        (!lean_is_exclusive(v___x_2812_)) as u8;
                                                    if v_isSharedCheck_2829_ == 0 {
                                                        v_unused_2830_ =
                                                            lean_ctor_get(v___x_2812_, 0);
                                                        lean_dec(v_unused_2830_);
                                                        v___x_2815_ = v___x_2812_;
                                                        v_isShared_2816_ = v_isSharedCheck_2829_;
                                                        state = 116;
                                                        continue;
                                                    } else {
                                                        lean_dec(v___x_2812_);
                                                        v___x_2815_ = lean_box(0);
                                                        v_isShared_2816_ = v_isSharedCheck_2829_;
                                                        state = 116;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_val_2811_);
                                                return v___x_2812_;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_2175_);
                                        return v___x_2809_;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_2181_);
                                lean_del_object(v___x_2166_);
                                v___x_2831_ =
                                    l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(
                                        v_arg_2180_,
                                        v_arg_2175_,
                                        v_a_2158_,
                                        v_a_2159_,
                                        v_a_2160_,
                                        v_a_2161_,
                                    );
                                return v___x_2831_;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2176_);
                        lean_del_object(v___x_2166_);
                        v___x_2832_ = l_Lean_Meta_evalNat(
                            v_arg_2175_,
                            v_a_2158_,
                            v_a_2159_,
                            v_a_2160_,
                            v_a_2161_,
                        );
                        if lean_obj_tag(v___x_2832_) == 0 {
                            v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
                            lean_inc(v_a_2833_);
                            if lean_obj_tag(v_a_2833_) == 0 {
                                return v___x_2832_;
                            } else {
                                v_isSharedCheck_2850_ = (!lean_is_exclusive(v___x_2832_)) as u8;
                                if v_isSharedCheck_2850_ == 0 {
                                    v_unused_2851_ = lean_ctor_get(v___x_2832_, 0);
                                    lean_dec(v_unused_2851_);
                                    v___x_2835_ = v___x_2832_;
                                    v_isShared_2836_ = v_isSharedCheck_2850_;
                                    state = 120;
                                    continue;
                                } else {
                                    lean_dec(v___x_2832_);
                                    v___x_2835_ = lean_box(0);
                                    v_isShared_2836_ = v_isSharedCheck_2850_;
                                    state = 120;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_2832_;
                        }
                    }
                }
            }
            2 => {
                v___x_2169_ = lean_box(0);
                if v_isShared_2167_ == 0 {
                    lean_ctor_set(v___x_2166_, 0, v___x_2169_);
                    v___x_2171_ = v___x_2166_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
                    v___x_2171_ = v_reuseFailAlloc_2172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2171_;
            }
            4 => {
                v___x_2236_ = (lean_unbox(v_a_2232_) as u8);
                lean_dec(v_a_2232_);
                if v___x_2236_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2237_ = lean_box(0);
                    if v_isShared_2235_ == 0 {
                        lean_ctor_set(v___x_2234_, 0, v___x_2237_);
                        v___x_2239_ = v___x_2234_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
                        v___x_2239_ = v_reuseFailAlloc_2240_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2234_);
                    v___x_2241_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2241_) == 0 {
                        v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
                        lean_inc(v_a_2242_);
                        if lean_obj_tag(v_a_2242_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2241_;
                        } else {
                            lean_dec_ref_known(v___x_2241_, 1);
                            v_val_2243_ = lean_ctor_get(v_a_2242_, 0);
                            lean_inc(v_val_2243_);
                            lean_dec_ref_known(v_a_2242_, 1);
                            v___x_2244_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2244_) == 0 {
                                v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
                                lean_inc(v_a_2245_);
                                if lean_obj_tag(v_a_2245_) == 0 {
                                    lean_dec(v_val_2243_);
                                    return v___x_2244_;
                                } else {
                                    v_isSharedCheck_2261_ = (!lean_is_exclusive(v___x_2244_)) as u8;
                                    if v_isSharedCheck_2261_ == 0 {
                                        v_unused_2262_ = lean_ctor_get(v___x_2244_, 0);
                                        lean_dec(v_unused_2262_);
                                        v___x_2247_ = v___x_2244_;
                                        v_isShared_2248_ = v_isSharedCheck_2261_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2244_);
                                        v___x_2247_ = lean_box(0);
                                        v_isShared_2248_ = v_isSharedCheck_2261_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2243_);
                                return v___x_2244_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2241_;
                    }
                }
            }
            5 => {
                return v___x_2239_;
            }
            6 => {
                v_val_2249_ = lean_ctor_get(v_a_2245_, 0);
                v_isSharedCheck_2260_ = (!lean_is_exclusive(v_a_2245_)) as u8;
                if v_isSharedCheck_2260_ == 0 {
                    v___x_2251_ = v_a_2245_;
                    v_isShared_2252_ = v_isSharedCheck_2260_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_val_2249_);
                    lean_dec(v_a_2245_);
                    v___x_2251_ = lean_box(0);
                    v_isShared_2252_ = v_isSharedCheck_2260_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2253_ = lean_nat_add(v_val_2243_, v_val_2249_);
                lean_dec(v_val_2249_);
                lean_dec(v_val_2243_);
                if v_isShared_2252_ == 0 {
                    lean_ctor_set(v___x_2251_, 0, v___x_2253_);
                    v___x_2255_ = v___x_2251_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2253_);
                    v___x_2255_ = v_reuseFailAlloc_2259_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2248_ == 0 {
                    lean_ctor_set(v___x_2247_, 0, v___x_2255_);
                    v___x_2257_ = v___x_2247_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
                    v___x_2257_ = v_reuseFailAlloc_2258_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2257_;
            }
            10 => {
                if v_isShared_2267_ == 0 {
                    v___x_2269_ = v___x_2266_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
                    v___x_2269_ = v_reuseFailAlloc_2270_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2269_;
            }
            12 => {
                v___x_2277_ = (lean_unbox(v_a_2273_) as u8);
                lean_dec(v_a_2273_);
                if v___x_2277_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2278_ = lean_box(0);
                    if v_isShared_2276_ == 0 {
                        lean_ctor_set(v___x_2275_, 0, v___x_2278_);
                        v___x_2280_ = v___x_2275_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
                        v___x_2280_ = v_reuseFailAlloc_2281_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2275_);
                    v___x_2282_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2282_) == 0 {
                        v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
                        lean_inc(v_a_2283_);
                        if lean_obj_tag(v_a_2283_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2282_;
                        } else {
                            lean_dec_ref_known(v___x_2282_, 1);
                            v_val_2284_ = lean_ctor_get(v_a_2283_, 0);
                            lean_inc(v_val_2284_);
                            lean_dec_ref_known(v_a_2283_, 1);
                            v___x_2285_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2285_) == 0 {
                                v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
                                lean_inc(v_a_2286_);
                                if lean_obj_tag(v_a_2286_) == 0 {
                                    lean_dec(v_val_2284_);
                                    return v___x_2285_;
                                } else {
                                    v_isSharedCheck_2302_ = (!lean_is_exclusive(v___x_2285_)) as u8;
                                    if v_isSharedCheck_2302_ == 0 {
                                        v_unused_2303_ = lean_ctor_get(v___x_2285_, 0);
                                        lean_dec(v_unused_2303_);
                                        v___x_2288_ = v___x_2285_;
                                        v_isShared_2289_ = v_isSharedCheck_2302_;
                                        state = 14;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2285_);
                                        v___x_2288_ = lean_box(0);
                                        v_isShared_2289_ = v_isSharedCheck_2302_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2284_);
                                return v___x_2285_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2282_;
                    }
                }
            }
            13 => {
                return v___x_2280_;
            }
            14 => {
                v_val_2290_ = lean_ctor_get(v_a_2286_, 0);
                v_isSharedCheck_2301_ = (!lean_is_exclusive(v_a_2286_)) as u8;
                if v_isSharedCheck_2301_ == 0 {
                    v___x_2292_ = v_a_2286_;
                    v_isShared_2293_ = v_isSharedCheck_2301_;
                    state = 15;
                    continue;
                } else {
                    lean_inc(v_val_2290_);
                    lean_dec(v_a_2286_);
                    v___x_2292_ = lean_box(0);
                    v_isShared_2293_ = v_isSharedCheck_2301_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2294_ = lean_nat_sub(v_val_2284_, v_val_2290_);
                lean_dec(v_val_2290_);
                lean_dec(v_val_2284_);
                if v_isShared_2293_ == 0 {
                    lean_ctor_set(v___x_2292_, 0, v___x_2294_);
                    v___x_2296_ = v___x_2292_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2294_);
                    v___x_2296_ = v_reuseFailAlloc_2300_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2289_ == 0 {
                    lean_ctor_set(v___x_2288_, 0, v___x_2296_);
                    v___x_2298_ = v___x_2288_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
                    v___x_2298_ = v_reuseFailAlloc_2299_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2298_;
            }
            18 => {
                if v_isShared_2308_ == 0 {
                    v___x_2310_ = v___x_2307_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
                    v___x_2310_ = v_reuseFailAlloc_2311_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2310_;
            }
            20 => {
                v___x_2318_ = (lean_unbox(v_a_2314_) as u8);
                lean_dec(v_a_2314_);
                if v___x_2318_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2319_ = lean_box(0);
                    if v_isShared_2317_ == 0 {
                        lean_ctor_set(v___x_2316_, 0, v___x_2319_);
                        v___x_2321_ = v___x_2316_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
                        v___x_2321_ = v_reuseFailAlloc_2322_;
                        state = 21;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2316_);
                    v___x_2323_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2323_) == 0 {
                        v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
                        lean_inc(v_a_2324_);
                        if lean_obj_tag(v_a_2324_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2323_;
                        } else {
                            lean_dec_ref_known(v___x_2323_, 1);
                            v_val_2325_ = lean_ctor_get(v_a_2324_, 0);
                            lean_inc(v_val_2325_);
                            lean_dec_ref_known(v_a_2324_, 1);
                            v___x_2326_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2326_) == 0 {
                                v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
                                lean_inc(v_a_2327_);
                                if lean_obj_tag(v_a_2327_) == 0 {
                                    lean_dec(v_val_2325_);
                                    return v___x_2326_;
                                } else {
                                    v_isSharedCheck_2343_ = (!lean_is_exclusive(v___x_2326_)) as u8;
                                    if v_isSharedCheck_2343_ == 0 {
                                        v_unused_2344_ = lean_ctor_get(v___x_2326_, 0);
                                        lean_dec(v_unused_2344_);
                                        v___x_2329_ = v___x_2326_;
                                        v_isShared_2330_ = v_isSharedCheck_2343_;
                                        state = 22;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2326_);
                                        v___x_2329_ = lean_box(0);
                                        v_isShared_2330_ = v_isSharedCheck_2343_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2325_);
                                return v___x_2326_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2323_;
                    }
                }
            }
            21 => {
                return v___x_2321_;
            }
            22 => {
                v_val_2331_ = lean_ctor_get(v_a_2327_, 0);
                v_isSharedCheck_2342_ = (!lean_is_exclusive(v_a_2327_)) as u8;
                if v_isSharedCheck_2342_ == 0 {
                    v___x_2333_ = v_a_2327_;
                    v_isShared_2334_ = v_isSharedCheck_2342_;
                    state = 23;
                    continue;
                } else {
                    lean_inc(v_val_2331_);
                    lean_dec(v_a_2327_);
                    v___x_2333_ = lean_box(0);
                    v_isShared_2334_ = v_isSharedCheck_2342_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_2335_ = lean_nat_mul(v_val_2325_, v_val_2331_);
                lean_dec(v_val_2331_);
                lean_dec(v_val_2325_);
                if v_isShared_2334_ == 0 {
                    lean_ctor_set(v___x_2333_, 0, v___x_2335_);
                    v___x_2337_ = v___x_2333_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2335_);
                    v___x_2337_ = v_reuseFailAlloc_2341_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_2330_ == 0 {
                    lean_ctor_set(v___x_2329_, 0, v___x_2337_);
                    v___x_2339_ = v___x_2329_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
                    v___x_2339_ = v_reuseFailAlloc_2340_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2339_;
            }
            26 => {
                if v_isShared_2349_ == 0 {
                    v___x_2351_ = v___x_2348_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
                    v___x_2351_ = v_reuseFailAlloc_2352_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2351_;
            }
            28 => {
                v___x_2359_ = (lean_unbox(v_a_2355_) as u8);
                lean_dec(v_a_2355_);
                if v___x_2359_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2360_ = lean_box(0);
                    if v_isShared_2358_ == 0 {
                        lean_ctor_set(v___x_2357_, 0, v___x_2360_);
                        v___x_2362_ = v___x_2357_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
                        v___x_2362_ = v_reuseFailAlloc_2363_;
                        state = 29;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2357_);
                    v___x_2364_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2364_) == 0 {
                        v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
                        lean_inc(v_a_2365_);
                        if lean_obj_tag(v_a_2365_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2364_;
                        } else {
                            lean_dec_ref_known(v___x_2364_, 1);
                            v_val_2366_ = lean_ctor_get(v_a_2365_, 0);
                            lean_inc(v_val_2366_);
                            lean_dec_ref_known(v_a_2365_, 1);
                            v___x_2367_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2367_) == 0 {
                                v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
                                lean_inc(v_a_2368_);
                                if lean_obj_tag(v_a_2368_) == 0 {
                                    lean_dec(v_val_2366_);
                                    return v___x_2367_;
                                } else {
                                    v_isSharedCheck_2384_ = (!lean_is_exclusive(v___x_2367_)) as u8;
                                    if v_isSharedCheck_2384_ == 0 {
                                        v_unused_2385_ = lean_ctor_get(v___x_2367_, 0);
                                        lean_dec(v_unused_2385_);
                                        v___x_2370_ = v___x_2367_;
                                        v_isShared_2371_ = v_isSharedCheck_2384_;
                                        state = 30;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2367_);
                                        v___x_2370_ = lean_box(0);
                                        v_isShared_2371_ = v_isSharedCheck_2384_;
                                        state = 30;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2366_);
                                return v___x_2367_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2364_;
                    }
                }
            }
            29 => {
                return v___x_2362_;
            }
            30 => {
                v_val_2372_ = lean_ctor_get(v_a_2368_, 0);
                v_isSharedCheck_2383_ = (!lean_is_exclusive(v_a_2368_)) as u8;
                if v_isSharedCheck_2383_ == 0 {
                    v___x_2374_ = v_a_2368_;
                    v_isShared_2375_ = v_isSharedCheck_2383_;
                    state = 31;
                    continue;
                } else {
                    lean_inc(v_val_2372_);
                    lean_dec(v_a_2368_);
                    v___x_2374_ = lean_box(0);
                    v_isShared_2375_ = v_isSharedCheck_2383_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_2376_ = lean_nat_div(v_val_2366_, v_val_2372_);
                lean_dec(v_val_2372_);
                lean_dec(v_val_2366_);
                if v_isShared_2375_ == 0 {
                    lean_ctor_set(v___x_2374_, 0, v___x_2376_);
                    v___x_2378_ = v___x_2374_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2376_);
                    v___x_2378_ = v_reuseFailAlloc_2382_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2371_ == 0 {
                    lean_ctor_set(v___x_2370_, 0, v___x_2378_);
                    v___x_2380_ = v___x_2370_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
                    v___x_2380_ = v_reuseFailAlloc_2381_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2380_;
            }
            34 => {
                if v_isShared_2390_ == 0 {
                    v___x_2392_ = v___x_2389_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
                    v___x_2392_ = v_reuseFailAlloc_2393_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2392_;
            }
            36 => {
                v___x_2400_ = (lean_unbox(v_a_2396_) as u8);
                lean_dec(v_a_2396_);
                if v___x_2400_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2401_ = lean_box(0);
                    if v_isShared_2399_ == 0 {
                        lean_ctor_set(v___x_2398_, 0, v___x_2401_);
                        v___x_2403_ = v___x_2398_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
                        v___x_2403_ = v_reuseFailAlloc_2404_;
                        state = 37;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2398_);
                    v___x_2405_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2405_) == 0 {
                        v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
                        lean_inc(v_a_2406_);
                        if lean_obj_tag(v_a_2406_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2405_;
                        } else {
                            lean_dec_ref_known(v___x_2405_, 1);
                            v_val_2407_ = lean_ctor_get(v_a_2406_, 0);
                            lean_inc(v_val_2407_);
                            lean_dec_ref_known(v_a_2406_, 1);
                            v___x_2408_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2408_) == 0 {
                                v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
                                lean_inc(v_a_2409_);
                                if lean_obj_tag(v_a_2409_) == 0 {
                                    lean_dec(v_val_2407_);
                                    return v___x_2408_;
                                } else {
                                    v_isSharedCheck_2425_ = (!lean_is_exclusive(v___x_2408_)) as u8;
                                    if v_isSharedCheck_2425_ == 0 {
                                        v_unused_2426_ = lean_ctor_get(v___x_2408_, 0);
                                        lean_dec(v_unused_2426_);
                                        v___x_2411_ = v___x_2408_;
                                        v_isShared_2412_ = v_isSharedCheck_2425_;
                                        state = 38;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2408_);
                                        v___x_2411_ = lean_box(0);
                                        v_isShared_2412_ = v_isSharedCheck_2425_;
                                        state = 38;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2407_);
                                return v___x_2408_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2405_;
                    }
                }
            }
            37 => {
                return v___x_2403_;
            }
            38 => {
                v_val_2413_ = lean_ctor_get(v_a_2409_, 0);
                v_isSharedCheck_2424_ = (!lean_is_exclusive(v_a_2409_)) as u8;
                if v_isSharedCheck_2424_ == 0 {
                    v___x_2415_ = v_a_2409_;
                    v_isShared_2416_ = v_isSharedCheck_2424_;
                    state = 39;
                    continue;
                } else {
                    lean_inc(v_val_2413_);
                    lean_dec(v_a_2409_);
                    v___x_2415_ = lean_box(0);
                    v_isShared_2416_ = v_isSharedCheck_2424_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_2417_ = lean_nat_mod(v_val_2407_, v_val_2413_);
                lean_dec(v_val_2413_);
                lean_dec(v_val_2407_);
                if v_isShared_2416_ == 0 {
                    lean_ctor_set(v___x_2415_, 0, v___x_2417_);
                    v___x_2419_ = v___x_2415_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2417_);
                    v___x_2419_ = v_reuseFailAlloc_2423_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2412_ == 0 {
                    lean_ctor_set(v___x_2411_, 0, v___x_2419_);
                    v___x_2421_ = v___x_2411_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2421_;
            }
            42 => {
                if v_isShared_2431_ == 0 {
                    v___x_2433_ = v___x_2430_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
                    v___x_2433_ = v_reuseFailAlloc_2434_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_2433_;
            }
            44 => {
                v___x_2441_ = (lean_unbox(v_a_2437_) as u8);
                lean_dec(v_a_2437_);
                if v___x_2441_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2442_ = lean_box(0);
                    if v_isShared_2440_ == 0 {
                        lean_ctor_set(v___x_2439_, 0, v___x_2442_);
                        v___x_2444_ = v___x_2439_;
                        state = 45;
                        continue;
                    } else {
                        v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
                        v___x_2444_ = v_reuseFailAlloc_2445_;
                        state = 45;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2439_);
                    v___x_2446_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(
                        v_arg_2180_,
                        v_arg_2175_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    return v___x_2446_;
                }
            }
            45 => {
                return v___x_2444_;
            }
            46 => {
                if v_isShared_2451_ == 0 {
                    v___x_2453_ = v___x_2450_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
                    v___x_2453_ = v_reuseFailAlloc_2454_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_2453_;
            }
            48 => {
                v___x_2461_ = (lean_unbox(v_a_2457_) as u8);
                lean_dec(v_a_2457_);
                if v___x_2461_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2462_ = lean_box(0);
                    if v_isShared_2460_ == 0 {
                        lean_ctor_set(v___x_2459_, 0, v___x_2462_);
                        v___x_2464_ = v___x_2459_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
                        v___x_2464_ = v_reuseFailAlloc_2465_;
                        state = 49;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2459_);
                    v___x_2466_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(
                        v_arg_2180_,
                        v_arg_2175_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    return v___x_2466_;
                }
            }
            49 => {
                return v___x_2464_;
            }
            50 => {
                if v_isShared_2471_ == 0 {
                    v___x_2473_ = v___x_2470_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
                    v___x_2473_ = v_reuseFailAlloc_2474_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_2473_;
            }
            52 => {
                v___x_2481_ = (lean_unbox(v_a_2477_) as u8);
                lean_dec(v_a_2477_);
                if v___x_2481_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2482_ = lean_box(0);
                    if v_isShared_2480_ == 0 {
                        lean_ctor_set(v___x_2479_, 0, v___x_2482_);
                        v___x_2484_ = v___x_2479_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
                        v___x_2484_ = v_reuseFailAlloc_2485_;
                        state = 53;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2479_);
                    v___x_2486_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2486_) == 0 {
                        v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
                        lean_inc(v_a_2487_);
                        if lean_obj_tag(v_a_2487_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2486_;
                        } else {
                            lean_dec_ref_known(v___x_2486_, 1);
                            v_val_2488_ = lean_ctor_get(v_a_2487_, 0);
                            lean_inc(v_val_2488_);
                            lean_dec_ref_known(v_a_2487_, 1);
                            v___x_2489_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2489_) == 0 {
                                v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
                                lean_inc(v_a_2490_);
                                if lean_obj_tag(v_a_2490_) == 0 {
                                    lean_dec(v_val_2488_);
                                    return v___x_2489_;
                                } else {
                                    v_isSharedCheck_2506_ = (!lean_is_exclusive(v___x_2489_)) as u8;
                                    if v_isSharedCheck_2506_ == 0 {
                                        v_unused_2507_ = lean_ctor_get(v___x_2489_, 0);
                                        lean_dec(v_unused_2507_);
                                        v___x_2492_ = v___x_2489_;
                                        v_isShared_2493_ = v_isSharedCheck_2506_;
                                        state = 54;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2489_);
                                        v___x_2492_ = lean_box(0);
                                        v_isShared_2493_ = v_isSharedCheck_2506_;
                                        state = 54;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2488_);
                                return v___x_2489_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2486_;
                    }
                }
            }
            53 => {
                return v___x_2484_;
            }
            54 => {
                v_val_2494_ = lean_ctor_get(v_a_2490_, 0);
                v_isSharedCheck_2505_ = (!lean_is_exclusive(v_a_2490_)) as u8;
                if v_isSharedCheck_2505_ == 0 {
                    v___x_2496_ = v_a_2490_;
                    v_isShared_2497_ = v_isSharedCheck_2505_;
                    state = 55;
                    continue;
                } else {
                    lean_inc(v_val_2494_);
                    lean_dec(v_a_2490_);
                    v___x_2496_ = lean_box(0);
                    v_isShared_2497_ = v_isSharedCheck_2505_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                v___x_2498_ = lean_nat_add(v_val_2488_, v_val_2494_);
                lean_dec(v_val_2494_);
                lean_dec(v_val_2488_);
                if v_isShared_2497_ == 0 {
                    lean_ctor_set(v___x_2496_, 0, v___x_2498_);
                    v___x_2500_ = v___x_2496_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2498_);
                    v___x_2500_ = v_reuseFailAlloc_2504_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                if v_isShared_2493_ == 0 {
                    lean_ctor_set(v___x_2492_, 0, v___x_2500_);
                    v___x_2502_ = v___x_2492_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
                    v___x_2502_ = v_reuseFailAlloc_2503_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_2502_;
            }
            58 => {
                if v_isShared_2512_ == 0 {
                    v___x_2514_ = v___x_2511_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
                    v___x_2514_ = v_reuseFailAlloc_2515_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_2514_;
            }
            60 => {
                v___x_2522_ = (lean_unbox(v_a_2518_) as u8);
                lean_dec(v_a_2518_);
                if v___x_2522_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2523_ = lean_box(0);
                    if v_isShared_2521_ == 0 {
                        lean_ctor_set(v___x_2520_, 0, v___x_2523_);
                        v___x_2525_ = v___x_2520_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
                        v___x_2525_ = v_reuseFailAlloc_2526_;
                        state = 61;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2520_);
                    v___x_2527_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2527_) == 0 {
                        v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
                        lean_inc(v_a_2528_);
                        if lean_obj_tag(v_a_2528_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2527_;
                        } else {
                            lean_dec_ref_known(v___x_2527_, 1);
                            v_val_2529_ = lean_ctor_get(v_a_2528_, 0);
                            lean_inc(v_val_2529_);
                            lean_dec_ref_known(v_a_2528_, 1);
                            v___x_2530_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2530_) == 0 {
                                v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
                                lean_inc(v_a_2531_);
                                if lean_obj_tag(v_a_2531_) == 0 {
                                    lean_dec(v_val_2529_);
                                    return v___x_2530_;
                                } else {
                                    v_isSharedCheck_2547_ = (!lean_is_exclusive(v___x_2530_)) as u8;
                                    if v_isSharedCheck_2547_ == 0 {
                                        v_unused_2548_ = lean_ctor_get(v___x_2530_, 0);
                                        lean_dec(v_unused_2548_);
                                        v___x_2533_ = v___x_2530_;
                                        v_isShared_2534_ = v_isSharedCheck_2547_;
                                        state = 62;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2530_);
                                        v___x_2533_ = lean_box(0);
                                        v_isShared_2534_ = v_isSharedCheck_2547_;
                                        state = 62;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2529_);
                                return v___x_2530_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2527_;
                    }
                }
            }
            61 => {
                return v___x_2525_;
            }
            62 => {
                v_val_2535_ = lean_ctor_get(v_a_2531_, 0);
                v_isSharedCheck_2546_ = (!lean_is_exclusive(v_a_2531_)) as u8;
                if v_isSharedCheck_2546_ == 0 {
                    v___x_2537_ = v_a_2531_;
                    v_isShared_2538_ = v_isSharedCheck_2546_;
                    state = 63;
                    continue;
                } else {
                    lean_inc(v_val_2535_);
                    lean_dec(v_a_2531_);
                    v___x_2537_ = lean_box(0);
                    v_isShared_2538_ = v_isSharedCheck_2546_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                v___x_2539_ = lean_nat_sub(v_val_2529_, v_val_2535_);
                lean_dec(v_val_2535_);
                lean_dec(v_val_2529_);
                if v_isShared_2538_ == 0 {
                    lean_ctor_set(v___x_2537_, 0, v___x_2539_);
                    v___x_2541_ = v___x_2537_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2539_);
                    v___x_2541_ = v_reuseFailAlloc_2545_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                if v_isShared_2534_ == 0 {
                    lean_ctor_set(v___x_2533_, 0, v___x_2541_);
                    v___x_2543_ = v___x_2533_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
                    v___x_2543_ = v_reuseFailAlloc_2544_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2543_;
            }
            66 => {
                if v_isShared_2553_ == 0 {
                    v___x_2555_ = v___x_2552_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
                    v___x_2555_ = v_reuseFailAlloc_2556_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2555_;
            }
            68 => {
                v___x_2563_ = (lean_unbox(v_a_2559_) as u8);
                lean_dec(v_a_2559_);
                if v___x_2563_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2564_ = lean_box(0);
                    if v_isShared_2562_ == 0 {
                        lean_ctor_set(v___x_2561_, 0, v___x_2564_);
                        v___x_2566_ = v___x_2561_;
                        state = 69;
                        continue;
                    } else {
                        v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
                        v___x_2566_ = v_reuseFailAlloc_2567_;
                        state = 69;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2561_);
                    v___x_2568_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2568_) == 0 {
                        v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
                        lean_inc(v_a_2569_);
                        if lean_obj_tag(v_a_2569_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2568_;
                        } else {
                            lean_dec_ref_known(v___x_2568_, 1);
                            v_val_2570_ = lean_ctor_get(v_a_2569_, 0);
                            lean_inc(v_val_2570_);
                            lean_dec_ref_known(v_a_2569_, 1);
                            v___x_2571_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2571_) == 0 {
                                v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
                                lean_inc(v_a_2572_);
                                if lean_obj_tag(v_a_2572_) == 0 {
                                    lean_dec(v_val_2570_);
                                    return v___x_2571_;
                                } else {
                                    v_isSharedCheck_2588_ = (!lean_is_exclusive(v___x_2571_)) as u8;
                                    if v_isSharedCheck_2588_ == 0 {
                                        v_unused_2589_ = lean_ctor_get(v___x_2571_, 0);
                                        lean_dec(v_unused_2589_);
                                        v___x_2574_ = v___x_2571_;
                                        v_isShared_2575_ = v_isSharedCheck_2588_;
                                        state = 70;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2571_);
                                        v___x_2574_ = lean_box(0);
                                        v_isShared_2575_ = v_isSharedCheck_2588_;
                                        state = 70;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2570_);
                                return v___x_2571_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2568_;
                    }
                }
            }
            69 => {
                return v___x_2566_;
            }
            70 => {
                v_val_2576_ = lean_ctor_get(v_a_2572_, 0);
                v_isSharedCheck_2587_ = (!lean_is_exclusive(v_a_2572_)) as u8;
                if v_isSharedCheck_2587_ == 0 {
                    v___x_2578_ = v_a_2572_;
                    v_isShared_2579_ = v_isSharedCheck_2587_;
                    state = 71;
                    continue;
                } else {
                    lean_inc(v_val_2576_);
                    lean_dec(v_a_2572_);
                    v___x_2578_ = lean_box(0);
                    v_isShared_2579_ = v_isSharedCheck_2587_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                v___x_2580_ = lean_nat_mul(v_val_2570_, v_val_2576_);
                lean_dec(v_val_2576_);
                lean_dec(v_val_2570_);
                if v_isShared_2579_ == 0 {
                    lean_ctor_set(v___x_2578_, 0, v___x_2580_);
                    v___x_2582_ = v___x_2578_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2580_);
                    v___x_2582_ = v_reuseFailAlloc_2586_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                if v_isShared_2575_ == 0 {
                    lean_ctor_set(v___x_2574_, 0, v___x_2582_);
                    v___x_2584_ = v___x_2574_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_2584_;
            }
            74 => {
                if v_isShared_2594_ == 0 {
                    v___x_2596_ = v___x_2593_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
                    v___x_2596_ = v_reuseFailAlloc_2597_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                return v___x_2596_;
            }
            76 => {
                v___x_2604_ = (lean_unbox(v_a_2600_) as u8);
                lean_dec(v_a_2600_);
                if v___x_2604_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2605_ = lean_box(0);
                    if v_isShared_2603_ == 0 {
                        lean_ctor_set(v___x_2602_, 0, v___x_2605_);
                        v___x_2607_ = v___x_2602_;
                        state = 77;
                        continue;
                    } else {
                        v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
                        v___x_2607_ = v_reuseFailAlloc_2608_;
                        state = 77;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2602_);
                    v___x_2609_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2609_) == 0 {
                        v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
                        lean_inc(v_a_2610_);
                        if lean_obj_tag(v_a_2610_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2609_;
                        } else {
                            lean_dec_ref_known(v___x_2609_, 1);
                            v_val_2611_ = lean_ctor_get(v_a_2610_, 0);
                            lean_inc(v_val_2611_);
                            lean_dec_ref_known(v_a_2610_, 1);
                            v___x_2612_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2612_) == 0 {
                                v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
                                lean_inc(v_a_2613_);
                                if lean_obj_tag(v_a_2613_) == 0 {
                                    lean_dec(v_val_2611_);
                                    return v___x_2612_;
                                } else {
                                    v_isSharedCheck_2629_ = (!lean_is_exclusive(v___x_2612_)) as u8;
                                    if v_isSharedCheck_2629_ == 0 {
                                        v_unused_2630_ = lean_ctor_get(v___x_2612_, 0);
                                        lean_dec(v_unused_2630_);
                                        v___x_2615_ = v___x_2612_;
                                        v_isShared_2616_ = v_isSharedCheck_2629_;
                                        state = 78;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2612_);
                                        v___x_2615_ = lean_box(0);
                                        v_isShared_2616_ = v_isSharedCheck_2629_;
                                        state = 78;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2611_);
                                return v___x_2612_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2609_;
                    }
                }
            }
            77 => {
                return v___x_2607_;
            }
            78 => {
                v_val_2617_ = lean_ctor_get(v_a_2613_, 0);
                v_isSharedCheck_2628_ = (!lean_is_exclusive(v_a_2613_)) as u8;
                if v_isSharedCheck_2628_ == 0 {
                    v___x_2619_ = v_a_2613_;
                    v_isShared_2620_ = v_isSharedCheck_2628_;
                    state = 79;
                    continue;
                } else {
                    lean_inc(v_val_2617_);
                    lean_dec(v_a_2613_);
                    v___x_2619_ = lean_box(0);
                    v_isShared_2620_ = v_isSharedCheck_2628_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_2621_ = lean_nat_div(v_val_2611_, v_val_2617_);
                lean_dec(v_val_2617_);
                lean_dec(v_val_2611_);
                if v_isShared_2620_ == 0 {
                    lean_ctor_set(v___x_2619_, 0, v___x_2621_);
                    v___x_2623_ = v___x_2619_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2621_);
                    v___x_2623_ = v_reuseFailAlloc_2627_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                if v_isShared_2616_ == 0 {
                    lean_ctor_set(v___x_2615_, 0, v___x_2623_);
                    v___x_2625_ = v___x_2615_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
                    v___x_2625_ = v_reuseFailAlloc_2626_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_2625_;
            }
            82 => {
                if v_isShared_2635_ == 0 {
                    v___x_2637_ = v___x_2634_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
                    v___x_2637_ = v_reuseFailAlloc_2638_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                return v___x_2637_;
            }
            84 => {
                v___x_2645_ = (lean_unbox(v_a_2641_) as u8);
                lean_dec(v_a_2641_);
                if v___x_2645_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2646_ = lean_box(0);
                    if v_isShared_2644_ == 0 {
                        lean_ctor_set(v___x_2643_, 0, v___x_2646_);
                        v___x_2648_ = v___x_2643_;
                        state = 85;
                        continue;
                    } else {
                        v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
                        v___x_2648_ = v_reuseFailAlloc_2649_;
                        state = 85;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2643_);
                    v___x_2650_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    if lean_obj_tag(v___x_2650_) == 0 {
                        v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
                        lean_inc(v_a_2651_);
                        if lean_obj_tag(v_a_2651_) == 0 {
                            lean_dec_ref(v_arg_2175_);
                            return v___x_2650_;
                        } else {
                            lean_dec_ref_known(v___x_2650_, 1);
                            v_val_2652_ = lean_ctor_get(v_a_2651_, 0);
                            lean_inc(v_val_2652_);
                            lean_dec_ref_known(v_a_2651_, 1);
                            v___x_2653_ = l_Lean_Meta_evalNat(
                                v_arg_2175_,
                                v_a_2158_,
                                v_a_2159_,
                                v_a_2160_,
                                v_a_2161_,
                            );
                            if lean_obj_tag(v___x_2653_) == 0 {
                                v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
                                lean_inc(v_a_2654_);
                                if lean_obj_tag(v_a_2654_) == 0 {
                                    lean_dec(v_val_2652_);
                                    return v___x_2653_;
                                } else {
                                    v_isSharedCheck_2670_ = (!lean_is_exclusive(v___x_2653_)) as u8;
                                    if v_isSharedCheck_2670_ == 0 {
                                        v_unused_2671_ = lean_ctor_get(v___x_2653_, 0);
                                        lean_dec(v_unused_2671_);
                                        v___x_2656_ = v___x_2653_;
                                        v_isShared_2657_ = v_isSharedCheck_2670_;
                                        state = 86;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2653_);
                                        v___x_2656_ = lean_box(0);
                                        v_isShared_2657_ = v_isSharedCheck_2670_;
                                        state = 86;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2652_);
                                return v___x_2653_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2175_);
                        return v___x_2650_;
                    }
                }
            }
            85 => {
                return v___x_2648_;
            }
            86 => {
                v_val_2658_ = lean_ctor_get(v_a_2654_, 0);
                v_isSharedCheck_2669_ = (!lean_is_exclusive(v_a_2654_)) as u8;
                if v_isSharedCheck_2669_ == 0 {
                    v___x_2660_ = v_a_2654_;
                    v_isShared_2661_ = v_isSharedCheck_2669_;
                    state = 87;
                    continue;
                } else {
                    lean_inc(v_val_2658_);
                    lean_dec(v_a_2654_);
                    v___x_2660_ = lean_box(0);
                    v_isShared_2661_ = v_isSharedCheck_2669_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                v___x_2662_ = lean_nat_mod(v_val_2652_, v_val_2658_);
                lean_dec(v_val_2658_);
                lean_dec(v_val_2652_);
                if v_isShared_2661_ == 0 {
                    lean_ctor_set(v___x_2660_, 0, v___x_2662_);
                    v___x_2664_ = v___x_2660_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2662_);
                    v___x_2664_ = v_reuseFailAlloc_2668_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                if v_isShared_2657_ == 0 {
                    lean_ctor_set(v___x_2656_, 0, v___x_2664_);
                    v___x_2666_ = v___x_2656_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
                    v___x_2666_ = v_reuseFailAlloc_2667_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                return v___x_2666_;
            }
            90 => {
                if v_isShared_2676_ == 0 {
                    v___x_2678_ = v___x_2675_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
                    v___x_2678_ = v_reuseFailAlloc_2679_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_2678_;
            }
            92 => {
                v___x_2686_ = (lean_unbox(v_a_2682_) as u8);
                lean_dec(v_a_2682_);
                if v___x_2686_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    lean_dec_ref(v_arg_2175_);
                    v___x_2687_ = lean_box(0);
                    if v_isShared_2685_ == 0 {
                        lean_ctor_set(v___x_2684_, 0, v___x_2687_);
                        v___x_2689_ = v___x_2684_;
                        state = 93;
                        continue;
                    } else {
                        v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
                        v___x_2689_ = v_reuseFailAlloc_2690_;
                        state = 93;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2684_);
                    v___x_2691_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(
                        v_arg_2180_,
                        v_arg_2175_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    return v___x_2691_;
                }
            }
            93 => {
                return v___x_2689_;
            }
            94 => {
                if v_isShared_2696_ == 0 {
                    v___x_2698_ = v___x_2695_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
                    v___x_2698_ = v_reuseFailAlloc_2699_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                return v___x_2698_;
            }
            96 => {
                v___x_2706_ = (lean_unbox(v_a_2702_) as u8);
                lean_dec(v_a_2702_);
                if v___x_2706_ == 0 {
                    lean_dec_ref(v_arg_2180_);
                    v___x_2707_ = lean_box(0);
                    if v_isShared_2705_ == 0 {
                        lean_ctor_set(v___x_2704_, 0, v___x_2707_);
                        v___x_2709_ = v___x_2704_;
                        state = 97;
                        continue;
                    } else {
                        v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
                        v___x_2709_ = v_reuseFailAlloc_2710_;
                        state = 97;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2704_);
                    v___x_2711_ = l_Lean_Meta_evalNat(
                        v_arg_2180_,
                        v_a_2158_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                    );
                    return v___x_2711_;
                }
            }
            97 => {
                return v___x_2709_;
            }
            98 => {
                if v_isShared_2716_ == 0 {
                    v___x_2718_ = v___x_2715_;
                    state = 99;
                    continue;
                } else {
                    v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
                    v___x_2718_ = v_reuseFailAlloc_2719_;
                    state = 99;
                    continue;
                }
            }
            99 => {
                return v___x_2718_;
            }
            100 => {
                v_val_2729_ = lean_ctor_get(v_a_2725_, 0);
                v_isSharedCheck_2740_ = (!lean_is_exclusive(v_a_2725_)) as u8;
                if v_isSharedCheck_2740_ == 0 {
                    v___x_2731_ = v_a_2725_;
                    v_isShared_2732_ = v_isSharedCheck_2740_;
                    state = 101;
                    continue;
                } else {
                    lean_inc(v_val_2729_);
                    lean_dec(v_a_2725_);
                    v___x_2731_ = lean_box(0);
                    v_isShared_2732_ = v_isSharedCheck_2740_;
                    state = 101;
                    continue;
                }
            }
            101 => {
                v___x_2733_ = lean_nat_add(v_val_2723_, v_val_2729_);
                lean_dec(v_val_2729_);
                lean_dec(v_val_2723_);
                if v_isShared_2732_ == 0 {
                    lean_ctor_set(v___x_2731_, 0, v___x_2733_);
                    v___x_2735_ = v___x_2731_;
                    state = 102;
                    continue;
                } else {
                    v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2733_);
                    v___x_2735_ = v_reuseFailAlloc_2739_;
                    state = 102;
                    continue;
                }
            }
            102 => {
                if v_isShared_2728_ == 0 {
                    lean_ctor_set(v___x_2727_, 0, v___x_2735_);
                    v___x_2737_ = v___x_2727_;
                    state = 103;
                    continue;
                } else {
                    v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
                    v___x_2737_ = v_reuseFailAlloc_2738_;
                    state = 103;
                    continue;
                }
            }
            103 => {
                return v___x_2737_;
            }
            104 => {
                v_val_2751_ = lean_ctor_get(v_a_2747_, 0);
                v_isSharedCheck_2762_ = (!lean_is_exclusive(v_a_2747_)) as u8;
                if v_isSharedCheck_2762_ == 0 {
                    v___x_2753_ = v_a_2747_;
                    v_isShared_2754_ = v_isSharedCheck_2762_;
                    state = 105;
                    continue;
                } else {
                    lean_inc(v_val_2751_);
                    lean_dec(v_a_2747_);
                    v___x_2753_ = lean_box(0);
                    v_isShared_2754_ = v_isSharedCheck_2762_;
                    state = 105;
                    continue;
                }
            }
            105 => {
                v___x_2755_ = lean_nat_sub(v_val_2745_, v_val_2751_);
                lean_dec(v_val_2751_);
                lean_dec(v_val_2745_);
                if v_isShared_2754_ == 0 {
                    lean_ctor_set(v___x_2753_, 0, v___x_2755_);
                    v___x_2757_ = v___x_2753_;
                    state = 106;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2755_);
                    v___x_2757_ = v_reuseFailAlloc_2761_;
                    state = 106;
                    continue;
                }
            }
            106 => {
                if v_isShared_2750_ == 0 {
                    lean_ctor_set(v___x_2749_, 0, v___x_2757_);
                    v___x_2759_ = v___x_2749_;
                    state = 107;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
                    v___x_2759_ = v_reuseFailAlloc_2760_;
                    state = 107;
                    continue;
                }
            }
            107 => {
                return v___x_2759_;
            }
            108 => {
                v_val_2773_ = lean_ctor_get(v_a_2769_, 0);
                v_isSharedCheck_2784_ = (!lean_is_exclusive(v_a_2769_)) as u8;
                if v_isSharedCheck_2784_ == 0 {
                    v___x_2775_ = v_a_2769_;
                    v_isShared_2776_ = v_isSharedCheck_2784_;
                    state = 109;
                    continue;
                } else {
                    lean_inc(v_val_2773_);
                    lean_dec(v_a_2769_);
                    v___x_2775_ = lean_box(0);
                    v_isShared_2776_ = v_isSharedCheck_2784_;
                    state = 109;
                    continue;
                }
            }
            109 => {
                v___x_2777_ = lean_nat_mul(v_val_2767_, v_val_2773_);
                lean_dec(v_val_2773_);
                lean_dec(v_val_2767_);
                if v_isShared_2776_ == 0 {
                    lean_ctor_set(v___x_2775_, 0, v___x_2777_);
                    v___x_2779_ = v___x_2775_;
                    state = 110;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2777_);
                    v___x_2779_ = v_reuseFailAlloc_2783_;
                    state = 110;
                    continue;
                }
            }
            110 => {
                if v_isShared_2772_ == 0 {
                    lean_ctor_set(v___x_2771_, 0, v___x_2779_);
                    v___x_2781_ = v___x_2771_;
                    state = 111;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
                    v___x_2781_ = v_reuseFailAlloc_2782_;
                    state = 111;
                    continue;
                }
            }
            111 => {
                return v___x_2781_;
            }
            112 => {
                v_val_2795_ = lean_ctor_get(v_a_2791_, 0);
                v_isSharedCheck_2806_ = (!lean_is_exclusive(v_a_2791_)) as u8;
                if v_isSharedCheck_2806_ == 0 {
                    v___x_2797_ = v_a_2791_;
                    v_isShared_2798_ = v_isSharedCheck_2806_;
                    state = 113;
                    continue;
                } else {
                    lean_inc(v_val_2795_);
                    lean_dec(v_a_2791_);
                    v___x_2797_ = lean_box(0);
                    v_isShared_2798_ = v_isSharedCheck_2806_;
                    state = 113;
                    continue;
                }
            }
            113 => {
                v___x_2799_ = lean_nat_div(v_val_2789_, v_val_2795_);
                lean_dec(v_val_2795_);
                lean_dec(v_val_2789_);
                if v_isShared_2798_ == 0 {
                    lean_ctor_set(v___x_2797_, 0, v___x_2799_);
                    v___x_2801_ = v___x_2797_;
                    state = 114;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2799_);
                    v___x_2801_ = v_reuseFailAlloc_2805_;
                    state = 114;
                    continue;
                }
            }
            114 => {
                if v_isShared_2794_ == 0 {
                    lean_ctor_set(v___x_2793_, 0, v___x_2801_);
                    v___x_2803_ = v___x_2793_;
                    state = 115;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 115;
                    continue;
                }
            }
            115 => {
                return v___x_2803_;
            }
            116 => {
                v_val_2817_ = lean_ctor_get(v_a_2813_, 0);
                v_isSharedCheck_2828_ = (!lean_is_exclusive(v_a_2813_)) as u8;
                if v_isSharedCheck_2828_ == 0 {
                    v___x_2819_ = v_a_2813_;
                    v_isShared_2820_ = v_isSharedCheck_2828_;
                    state = 117;
                    continue;
                } else {
                    lean_inc(v_val_2817_);
                    lean_dec(v_a_2813_);
                    v___x_2819_ = lean_box(0);
                    v_isShared_2820_ = v_isSharedCheck_2828_;
                    state = 117;
                    continue;
                }
            }
            117 => {
                v___x_2821_ = lean_nat_mod(v_val_2811_, v_val_2817_);
                lean_dec(v_val_2817_);
                lean_dec(v_val_2811_);
                if v_isShared_2820_ == 0 {
                    lean_ctor_set(v___x_2819_, 0, v___x_2821_);
                    v___x_2823_ = v___x_2819_;
                    state = 118;
                    continue;
                } else {
                    v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2821_);
                    v___x_2823_ = v_reuseFailAlloc_2827_;
                    state = 118;
                    continue;
                }
            }
            118 => {
                if v_isShared_2816_ == 0 {
                    lean_ctor_set(v___x_2815_, 0, v___x_2823_);
                    v___x_2825_ = v___x_2815_;
                    state = 119;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
                    v___x_2825_ = v_reuseFailAlloc_2826_;
                    state = 119;
                    continue;
                }
            }
            119 => {
                return v___x_2825_;
            }
            120 => {
                v_val_2837_ = lean_ctor_get(v_a_2833_, 0);
                v_isSharedCheck_2849_ = (!lean_is_exclusive(v_a_2833_)) as u8;
                if v_isSharedCheck_2849_ == 0 {
                    v___x_2839_ = v_a_2833_;
                    v_isShared_2840_ = v_isSharedCheck_2849_;
                    state = 121;
                    continue;
                } else {
                    lean_inc(v_val_2837_);
                    lean_dec(v_a_2833_);
                    v___x_2839_ = lean_box(0);
                    v_isShared_2840_ = v_isSharedCheck_2849_;
                    state = 121;
                    continue;
                }
            }
            121 => {
                v___x_2841_ = lean_unsigned_to_nat(1);
                v___x_2842_ = lean_nat_add(v_val_2837_, v___x_2841_);
                lean_dec(v_val_2837_);
                if v_isShared_2840_ == 0 {
                    lean_ctor_set(v___x_2839_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2839_;
                    state = 122;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2842_);
                    v___x_2844_ = v_reuseFailAlloc_2848_;
                    state = 122;
                    continue;
                }
            }
            122 => {
                if v_isShared_2836_ == 0 {
                    lean_ctor_set(v___x_2835_, 0, v___x_2844_);
                    v___x_2846_ = v___x_2835_;
                    state = 123;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
                    v___x_2846_ = v_reuseFailAlloc_2847_;
                    state = 123;
                    continue;
                }
            }
            123 => {
                return v___x_2846_;
            }
            124 => {
                if v_isShared_2856_ == 0 {
                    v___x_2858_ = v___x_2855_;
                    state = 125;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
                    v___x_2858_ = v_reuseFailAlloc_2859_;
                    state = 125;
                    continue;
                }
            }
            125 => {
                return v___x_2858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_evalNat(
    mut v_e_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_expr_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2861_) {
                9 => {
                    v_a_2870_ = lean_ctor_get(v_e_2861_, 0);
                    lean_inc_ref(v_a_2870_);
                    lean_dec_ref_known(v_e_2861_, 1);
                    if lean_obj_tag(v_a_2870_) == 0 {
                        v_val_2871_ = lean_ctor_get(v_a_2870_, 0);
                        v_isSharedCheck_2879_ = (!lean_is_exclusive(v_a_2870_)) as u8;
                        if v_isSharedCheck_2879_ == 0 {
                            v___x_2873_ = v_a_2870_;
                            v_isShared_2874_ = v_isSharedCheck_2879_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_2871_);
                            lean_dec(v_a_2870_);
                            v___x_2873_ = lean_box(0);
                            v_isShared_2874_ = v_isSharedCheck_2879_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_2870_);
                        state = 1;
                        continue;
                    }
                }
                10 => {
                    v_expr_2880_ = lean_ctor_get(v_e_2861_, 1);
                    lean_inc_ref(v_expr_2880_);
                    lean_dec_ref_known(v_e_2861_, 2);
                    v_e_2861_ = v_expr_2880_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_declName_2882_ = lean_ctor_get(v_e_2861_, 0);
                    lean_inc(v_declName_2882_);
                    lean_dec_ref_known(v_e_2861_, 2);
                    if lean_obj_tag(v_declName_2882_) == 1 {
                        v_pre_2883_ = lean_ctor_get(v_declName_2882_, 0);
                        lean_inc(v_pre_2883_);
                        if lean_obj_tag(v_pre_2883_) == 1 {
                            v_pre_2884_ = lean_ctor_get(v_pre_2883_, 0);
                            if lean_obj_tag(v_pre_2884_) == 0 {
                                v_str_2885_ = lean_ctor_get(v_declName_2882_, 1);
                                lean_inc_ref(v_str_2885_);
                                lean_dec_ref_known(v_declName_2882_, 2);
                                v_str_2886_ = lean_ctor_get(v_pre_2883_, 1);
                                lean_inc_ref(v_str_2886_);
                                lean_dec_ref_known(v_pre_2883_, 2);
                                v___x_2887_ = l_Lean_Meta_evalNat___closed__0;
                                v___x_2888_ = lean_string_dec_eq(v_str_2886_, v___x_2887_);
                                lean_dec_ref(v_str_2886_);
                                if v___x_2888_ == 0 {
                                    lean_dec_ref(v_str_2885_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2889_ = l_Lean_Meta_evalNat___closed__1;
                                    v___x_2890_ = lean_string_dec_eq(v_str_2885_, v___x_2889_);
                                    lean_dec_ref(v_str_2885_);
                                    if v___x_2890_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_2891_ = l_Lean_Meta_evalNat___closed__2;
                                        v___x_2892_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_2892_, 0, v___x_2891_);
                                        return v___x_2892_;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v_pre_2883_, 2);
                                lean_dec_ref_known(v_declName_2882_, 2);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_pre_2883_);
                            lean_dec_ref_known(v_declName_2882_, 2);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_2882_);
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v___x_2893_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(
                        v_e_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_,
                    );
                    return v___x_2893_;
                }
                2 => {
                    v___x_2894_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(
                        v_e_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_,
                    );
                    return v___x_2894_;
                }
                _ => {
                    lean_dec_ref(v_e_2861_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2868_ = lean_box(0);
                v___x_2869_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2869_, 0, v___x_2868_);
                return v___x_2869_;
            }
            2 => {
                if v_isShared_2874_ == 0 {
                    lean_ctor_set_tag(v___x_2873_, 1);
                    v___x_2876_ = v___x_2873_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_val_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2878_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2877_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2877_, 0, v___x_2876_);
                return v___x_2877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(
    mut v_b_2895_: *mut LeanObject,
    mut v_n_2896_: *mut LeanObject,
    mut v_a_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
    mut v_a_2899_: *mut LeanObject,
    mut v_a_2900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: u8 = 0;
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v_val_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2924_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_unused_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_a_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2902_ =
                    l_Lean_Meta_evalNat(v_n_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
                if lean_obj_tag(v___x_2902_) == 0 {
                    v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
                    lean_inc(v_a_2903_);
                    if lean_obj_tag(v_a_2903_) == 0 {
                        lean_dec_ref(v_b_2895_);
                        return v___x_2902_;
                    } else {
                        lean_dec_ref_known(v___x_2902_, 1);
                        v_val_2904_ = lean_ctor_get(v_a_2903_, 0);
                        lean_inc_n(v_val_2904_, 2);
                        lean_dec_ref_known(v_a_2903_, 1);
                        v___x_2905_ = 1;
                        v___x_2906_ =
                            l_Lean_checkExponent(v_val_2904_, v___x_2905_, v_a_2899_, v_a_2900_);
                        if lean_obj_tag(v___x_2906_) == 0 {
                            v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
                            v_isSharedCheck_2935_ = (!lean_is_exclusive(v___x_2906_)) as u8;
                            if v_isSharedCheck_2935_ == 0 {
                                v___x_2909_ = v___x_2906_;
                                v_isShared_2910_ = v_isSharedCheck_2935_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2907_);
                                lean_dec(v___x_2906_);
                                v___x_2909_ = lean_box(0);
                                v_isShared_2910_ = v_isSharedCheck_2935_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_2904_);
                            lean_dec_ref(v_b_2895_);
                            v_a_2936_ = lean_ctor_get(v___x_2906_, 0);
                            v_isSharedCheck_2943_ = (!lean_is_exclusive(v___x_2906_)) as u8;
                            if v_isSharedCheck_2943_ == 0 {
                                v___x_2938_ = v___x_2906_;
                                v_isShared_2939_ = v_isSharedCheck_2943_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2936_);
                                lean_dec(v___x_2906_);
                                v___x_2938_ = lean_box(0);
                                v_isShared_2939_ = v_isSharedCheck_2943_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_b_2895_);
                    return v___x_2902_;
                }
            }
            1 => {
                v___x_2911_ = (lean_unbox(v_a_2907_) as u8);
                lean_dec(v_a_2907_);
                if v___x_2911_ == 0 {
                    lean_dec(v_val_2904_);
                    lean_dec_ref(v_b_2895_);
                    v___x_2912_ = lean_box(0);
                    if v_isShared_2910_ == 0 {
                        lean_ctor_set(v___x_2909_, 0, v___x_2912_);
                        v___x_2914_ = v___x_2909_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
                        v___x_2914_ = v_reuseFailAlloc_2915_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2909_);
                    v___x_2916_ =
                        l_Lean_Meta_evalNat(v_b_2895_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
                    if lean_obj_tag(v___x_2916_) == 0 {
                        v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
                        lean_inc(v_a_2917_);
                        if lean_obj_tag(v_a_2917_) == 0 {
                            lean_dec(v_val_2904_);
                            return v___x_2916_;
                        } else {
                            v_isSharedCheck_2933_ = (!lean_is_exclusive(v___x_2916_)) as u8;
                            if v_isSharedCheck_2933_ == 0 {
                                v_unused_2934_ = lean_ctor_get(v___x_2916_, 0);
                                lean_dec(v_unused_2934_);
                                v___x_2919_ = v___x_2916_;
                                v_isShared_2920_ = v_isSharedCheck_2933_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_2916_);
                                v___x_2919_ = lean_box(0);
                                v_isShared_2920_ = v_isSharedCheck_2933_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_2904_);
                        return v___x_2916_;
                    }
                }
            }
            2 => {
                return v___x_2914_;
            }
            3 => {
                v_val_2921_ = lean_ctor_get(v_a_2917_, 0);
                v_isSharedCheck_2932_ = (!lean_is_exclusive(v_a_2917_)) as u8;
                if v_isSharedCheck_2932_ == 0 {
                    v___x_2923_ = v_a_2917_;
                    v_isShared_2924_ = v_isSharedCheck_2932_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_val_2921_);
                    lean_dec(v_a_2917_);
                    v___x_2923_ = lean_box(0);
                    v_isShared_2924_ = v_isSharedCheck_2932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2925_ = lean_nat_pow(v_val_2921_, v_val_2904_);
                lean_dec(v_val_2904_);
                lean_dec(v_val_2921_);
                if v_isShared_2924_ == 0 {
                    lean_ctor_set(v___x_2923_, 0, v___x_2925_);
                    v___x_2927_ = v___x_2923_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2925_);
                    v___x_2927_ = v_reuseFailAlloc_2931_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2920_ == 0 {
                    lean_ctor_set(v___x_2919_, 0, v___x_2927_);
                    v___x_2929_ = v___x_2919_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
                    v___x_2929_ = v_reuseFailAlloc_2930_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2929_;
            }
            7 => {
                if v_isShared_2939_ == 0 {
                    v___x_2941_ = v___x_2938_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow___boxed(
    mut v_b_2944_: *mut LeanObject,
    mut v_n_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
    mut v_a_2948_: *mut LeanObject,
    mut v_a_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2951_: *mut LeanObject = core::ptr::null_mut();
    v_res_2951_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_evalPow(
        v_b_2944_, v_n_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_,
    );
    lean_dec(v_a_2949_);
    lean_dec_ref(v_a_2948_);
    lean_dec(v_a_2947_);
    lean_dec_ref(v_a_2946_);
    return v_res_2951_;
}
pub unsafe fn l_Lean_Meta_evalNat___boxed(
    mut v_e_2952_: *mut LeanObject,
    mut v_a_2953_: *mut LeanObject,
    mut v_a_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2958_: *mut LeanObject = core::ptr::null_mut();
    v_res_2958_ = l_Lean_Meta_evalNat(v_e_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
    lean_dec(v_a_2956_);
    lean_dec_ref(v_a_2955_);
    lean_dec(v_a_2954_);
    lean_dec_ref(v_a_2953_);
    return v_res_2958_;
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___boxed(
    mut v_e_2959_: *mut LeanObject,
    mut v_a_2960_: *mut LeanObject,
    mut v_a_2961_: *mut LeanObject,
    mut v_a_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2965_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit(
        v_e_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_,
    );
    lean_dec(v_a_2963_);
    lean_dec_ref(v_a_2962_);
    lean_dec(v_a_2961_);
    lean_dec_ref(v_a_2960_);
    return v_res_2965_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(
    mut v_k_2966_: *mut LeanObject,
    mut v_allowLevelAssignments_2967_: u8,
    mut v___y_2968_: *mut LeanObject,
    mut v___y_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2977_: u8 = 0;
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2981_: u8 = 0;
    let mut v_a_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2973_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_2967_,
                    v_k_2966_,
                    v___y_2968_,
                    v___y_2969_,
                    v___y_2970_,
                    v___y_2971_,
                );
                if lean_obj_tag(v___x_2973_) == 0 {
                    v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
                    v_isSharedCheck_2981_ = (!lean_is_exclusive(v___x_2973_)) as u8;
                    if v_isSharedCheck_2981_ == 0 {
                        v___x_2976_ = v___x_2973_;
                        v_isShared_2977_ = v_isSharedCheck_2981_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2974_);
                        lean_dec(v___x_2973_);
                        v___x_2976_ = lean_box(0);
                        v_isShared_2977_ = v_isSharedCheck_2981_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2982_ = lean_ctor_get(v___x_2973_, 0);
                    v_isSharedCheck_2989_ = (!lean_is_exclusive(v___x_2973_)) as u8;
                    if v_isSharedCheck_2989_ == 0 {
                        v___x_2984_ = v___x_2973_;
                        v_isShared_2985_ = v_isSharedCheck_2989_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2982_);
                        lean_dec(v___x_2973_);
                        v___x_2984_ = lean_box(0);
                        v_isShared_2985_ = v_isSharedCheck_2989_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2977_ == 0 {
                    v___x_2979_ = v___x_2976_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
                    v___x_2979_ = v_reuseFailAlloc_2980_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2979_;
            }
            3 => {
                if v_isShared_2985_ == 0 {
                    v___x_2987_ = v___x_2984_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
                    v___x_2987_ = v_reuseFailAlloc_2988_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg___boxed(
    mut v_k_2990_: *mut LeanObject,
    mut v_allowLevelAssignments_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_2997_: u8 = 0;
    let mut v_res_2998_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_2997_ = (lean_unbox(v_allowLevelAssignments_2991_) as u8);
    v_res_2998_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(
        v_k_2990_,
        v_allowLevelAssignments_boxed_2997_,
        v___y_2992_,
        v___y_2993_,
        v___y_2994_,
        v___y_2995_,
    );
    lean_dec(v___y_2995_);
    lean_dec_ref(v___y_2994_);
    lean_dec(v___y_2993_);
    lean_dec_ref(v___y_2992_);
    return v_res_2998_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(
    mut v_00_u03b1_2999_: *mut LeanObject,
    mut v_k_3000_: *mut LeanObject,
    mut v_allowLevelAssignments_3001_: u8,
    mut v___y_3002_: *mut LeanObject,
    mut v___y_3003_: *mut LeanObject,
    mut v___y_3004_: *mut LeanObject,
    mut v___y_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    v___x_3007_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(
        v_k_3000_,
        v_allowLevelAssignments_3001_,
        v___y_3002_,
        v___y_3003_,
        v___y_3004_,
        v___y_3005_,
    );
    return v___x_3007_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___boxed(
    mut v_00_u03b1_3008_: *mut LeanObject,
    mut v_k_3009_: *mut LeanObject,
    mut v_allowLevelAssignments_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
    mut v___y_3014_: *mut LeanObject,
    mut v___y_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3016_: u8 = 0;
    let mut v_res_3017_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3016_ = (lean_unbox(v_allowLevelAssignments_3010_) as u8);
    v_res_3017_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0(
        v_00_u03b1_3008_,
        v_k_3009_,
        v_allowLevelAssignments_boxed_3016_,
        v___y_3011_,
        v___y_3012_,
        v___y_3013_,
        v___y_3014_,
    );
    lean_dec(v___y_3014_);
    lean_dec_ref(v___y_3013_);
    lean_dec(v___y_3012_);
    lean_dec_ref(v___y_3011_);
    return v_res_3017_;
}
pub unsafe fn l_Lean_Meta_matchesInstance___lam__0(
    mut v___x_3018_: u8,
    mut v_e_3019_: *mut LeanObject,
    mut v_inst_3020_: *mut LeanObject,
    mut v___y_3021_: *mut LeanObject,
    mut v___y_3022_: *mut LeanObject,
    mut v___y_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3027_: u8 = 0;
    let mut v_ctxApprox_3028_: u8 = 0;
    let mut v_quasiPatternApprox_3029_: u8 = 0;
    let mut v_constApprox_3030_: u8 = 0;
    let mut v_isDefEqStuckEx_3031_: u8 = 0;
    let mut v_unificationHints_3032_: u8 = 0;
    let mut v_proofIrrelevance_3033_: u8 = 0;
    let mut v_assignSyntheticOpaque_3034_: u8 = 0;
    let mut v_offsetCnstrs_3035_: u8 = 0;
    let mut v_etaStruct_3036_: u8 = 0;
    let mut v_univApprox_3037_: u8 = 0;
    let mut v_iota_3038_: u8 = 0;
    let mut v_beta_3039_: u8 = 0;
    let mut v_proj_3040_: u8 = 0;
    let mut v_zeta_3041_: u8 = 0;
    let mut v_zetaDelta_3042_: u8 = 0;
    let mut v_zetaUnused_3043_: u8 = 0;
    let mut v_zetaHave_3044_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v_trackZetaDelta_3048_: u8 = 0;
    let mut v_zetaDeltaSet_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3055_: u8 = 0;
    let mut v_inTypeClassResolution_3056_: u8 = 0;
    let mut v_cacheInferType_3057_: u8 = 0;
    let mut v_config_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: u64 = 0;
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3064_: u64 = 0;
    let mut v___x_3065_: u64 = 0;
    let mut v___x_3066_: u64 = 0;
    let mut v___x_3067_: u64 = 0;
    let mut v_key_3068_: u64 = 0;
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3074_: u8 = 0;
    let mut v_unused_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3026_ = l_Lean_Meta_Context_config(v___y_3021_);
                v_foApprox_3027_ = lean_ctor_get_uint8(v___x_3026_, 0 as u32);
                v_ctxApprox_3028_ = lean_ctor_get_uint8(v___x_3026_, 1 as u32);
                v_quasiPatternApprox_3029_ = lean_ctor_get_uint8(v___x_3026_, 2 as u32);
                v_constApprox_3030_ = lean_ctor_get_uint8(v___x_3026_, 3 as u32);
                v_isDefEqStuckEx_3031_ = lean_ctor_get_uint8(v___x_3026_, 4 as u32);
                v_unificationHints_3032_ = lean_ctor_get_uint8(v___x_3026_, 5 as u32);
                v_proofIrrelevance_3033_ = lean_ctor_get_uint8(v___x_3026_, 6 as u32);
                v_assignSyntheticOpaque_3034_ = lean_ctor_get_uint8(v___x_3026_, 7 as u32);
                v_offsetCnstrs_3035_ = lean_ctor_get_uint8(v___x_3026_, 8 as u32);
                v_etaStruct_3036_ = lean_ctor_get_uint8(v___x_3026_, 10 as u32);
                v_univApprox_3037_ = lean_ctor_get_uint8(v___x_3026_, 11 as u32);
                v_iota_3038_ = lean_ctor_get_uint8(v___x_3026_, 12 as u32);
                v_beta_3039_ = lean_ctor_get_uint8(v___x_3026_, 13 as u32);
                v_proj_3040_ = lean_ctor_get_uint8(v___x_3026_, 14 as u32);
                v_zeta_3041_ = lean_ctor_get_uint8(v___x_3026_, 15 as u32);
                v_zetaDelta_3042_ = lean_ctor_get_uint8(v___x_3026_, 16 as u32);
                v_zetaUnused_3043_ = lean_ctor_get_uint8(v___x_3026_, 17 as u32);
                v_zetaHave_3044_ = lean_ctor_get_uint8(v___x_3026_, 18 as u32);
                v_isSharedCheck_3083_ = (!lean_is_exclusive(v___x_3026_)) as u8;
                if v_isSharedCheck_3083_ == 0 {
                    v___x_3046_ = v___x_3026_;
                    v_isShared_3047_ = v_isSharedCheck_3083_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_3026_);
                    v___x_3046_ = lean_box(0);
                    v_isShared_3047_ = v_isSharedCheck_3083_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_3048_ = lean_ctor_get_uint8(
                    v___y_3021_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3049_ = lean_ctor_get(v___y_3021_, 1);
                lean_inc(v_zetaDeltaSet_3049_);
                v_lctx_3050_ = lean_ctor_get(v___y_3021_, 2);
                lean_inc_ref(v_lctx_3050_);
                v_localInstances_3051_ = lean_ctor_get(v___y_3021_, 3);
                lean_inc_ref(v_localInstances_3051_);
                v_defEqCtx_x3f_3052_ = lean_ctor_get(v___y_3021_, 4);
                lean_inc(v_defEqCtx_x3f_3052_);
                v_synthPendingDepth_3053_ = lean_ctor_get(v___y_3021_, 5);
                lean_inc(v_synthPendingDepth_3053_);
                v_canUnfold_x3f_3054_ = lean_ctor_get(v___y_3021_, 6);
                lean_inc(v_canUnfold_x3f_3054_);
                v_univApprox_3055_ = lean_ctor_get_uint8(
                    v___y_3021_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3056_ = lean_ctor_get_uint8(
                    v___y_3021_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3057_ = lean_ctor_get_uint8(
                    v___y_3021_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_3047_ == 0 {
                    v_config_3059_ = v___x_3046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 0 as u32, v_foApprox_3027_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 1 as u32, v_ctxApprox_3028_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3082_,
                        2 as u32,
                        v_quasiPatternApprox_3029_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 3 as u32, v_constApprox_3030_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 4 as u32, v_isDefEqStuckEx_3031_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 5 as u32, v_unificationHints_3032_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 6 as u32, v_proofIrrelevance_3033_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3082_,
                        7 as u32,
                        v_assignSyntheticOpaque_3034_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 8 as u32, v_offsetCnstrs_3035_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 10 as u32, v_etaStruct_3036_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 11 as u32, v_univApprox_3037_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 12 as u32, v_iota_3038_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 13 as u32, v_beta_3039_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 14 as u32, v_proj_3040_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 15 as u32, v_zeta_3041_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 16 as u32, v_zetaDelta_3042_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 17 as u32, v_zetaUnused_3043_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3082_, 18 as u32, v_zetaHave_3044_);
                    v_config_3059_ = v_reuseFailAlloc_3082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_3059_, 9 as u32, v___x_3018_);
                v___x_3060_ = l_Lean_Meta_Context_configKey(v___y_3021_);
                v_isSharedCheck_3074_ = (!lean_is_exclusive(v___y_3021_)) as u8;
                if v_isSharedCheck_3074_ == 0 {
                    v_unused_3075_ = lean_ctor_get(v___y_3021_, 6);
                    lean_dec(v_unused_3075_);
                    v_unused_3076_ = lean_ctor_get(v___y_3021_, 5);
                    lean_dec(v_unused_3076_);
                    v_unused_3077_ = lean_ctor_get(v___y_3021_, 4);
                    lean_dec(v_unused_3077_);
                    v_unused_3078_ = lean_ctor_get(v___y_3021_, 3);
                    lean_dec(v_unused_3078_);
                    v_unused_3079_ = lean_ctor_get(v___y_3021_, 2);
                    lean_dec(v_unused_3079_);
                    v_unused_3080_ = lean_ctor_get(v___y_3021_, 1);
                    lean_dec(v_unused_3080_);
                    v_unused_3081_ = lean_ctor_get(v___y_3021_, 0);
                    lean_dec(v_unused_3081_);
                    v___x_3062_ = v___y_3021_;
                    v_isShared_3063_ = v_isSharedCheck_3074_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___y_3021_);
                    v___x_3062_ = lean_box(0);
                    v_isShared_3063_ = v_isSharedCheck_3074_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3064_ = 3u64;
                v___x_3065_ = lean_uint64_shift_right(v___x_3060_, v___x_3064_);
                v___x_3066_ = lean_uint64_shift_left(v___x_3065_, v___x_3064_);
                v___x_3067_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3018_);
                v_key_3068_ = lean_uint64_lor(v___x_3066_, v___x_3067_);
                v___x_3069_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_3069_, 0, v_config_3059_);
                lean_ctor_set_uint64(
                    v___x_3069_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_3068_,
                );
                if v_isShared_3063_ == 0 {
                    lean_ctor_set(v___x_3062_, 0, v___x_3069_);
                    v___x_3071_ = v___x_3062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3069_);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_zetaDeltaSet_3049_);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_lctx_3050_);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 3, v_localInstances_3051_);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 4, v_defEqCtx_x3f_3052_);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 5, v_synthPendingDepth_3053_);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 6, v_canUnfold_x3f_3054_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3073_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_trackZetaDelta_3048_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3073_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v_univApprox_3055_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3073_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_3056_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3073_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_3057_,
                    );
                    v___x_3071_ = v_reuseFailAlloc_3073_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3072_ = l_Lean_Meta_isExprDefEq(
                    v_e_3019_,
                    v_inst_3020_,
                    v___x_3071_,
                    v___y_3022_,
                    v___y_3023_,
                    v___y_3024_,
                );
                lean_dec_ref(v___x_3071_);
                return v___x_3072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchesInstance___lam__0___boxed(
    mut v___x_3084_: *mut LeanObject,
    mut v_e_3085_: *mut LeanObject,
    mut v_inst_3086_: *mut LeanObject,
    mut v___y_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_680__boxed_3092_: u8 = 0;
    let mut v_res_3093_: *mut LeanObject = core::ptr::null_mut();
    v___x_680__boxed_3092_ = (lean_unbox(v___x_3084_) as u8);
    v_res_3093_ = l_Lean_Meta_matchesInstance___lam__0(
        v___x_680__boxed_3092_,
        v_e_3085_,
        v_inst_3086_,
        v___y_3087_,
        v___y_3088_,
        v___y_3089_,
        v___y_3090_,
    );
    lean_dec(v___y_3090_);
    lean_dec_ref(v___y_3089_);
    lean_dec(v___y_3088_);
    return v_res_3093_;
}
pub unsafe fn l_Lean_Meta_matchesInstance(
    mut v_e_3094_: *mut LeanObject,
    mut v_inst_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    v___x_3101_ = 3;
    v___x_3102_ = lean_box((v___x_3101_) as usize);
    v___f_3103_ = lean_alloc_closure(
        l_Lean_Meta_matchesInstance___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_3103_, 0, v___x_3102_);
    lean_closure_set(v___f_3103_, 1, v_e_3094_);
    lean_closure_set(v___f_3103_, 2, v_inst_3095_);
    v___x_3104_ = 0;
    v___x_3105_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(
        v___f_3103_,
        v___x_3104_,
        v_a_3096_,
        v_a_3097_,
        v_a_3098_,
        v_a_3099_,
    );
    return v___x_3105_;
}
pub unsafe fn l_Lean_Meta_matchesInstance___boxed(
    mut v_e_3106_: *mut LeanObject,
    mut v_inst_3107_: *mut LeanObject,
    mut v_a_3108_: *mut LeanObject,
    mut v_a_3109_: *mut LeanObject,
    mut v_a_3110_: *mut LeanObject,
    mut v_a_3111_: *mut LeanObject,
    mut v_a_3112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3113_: *mut LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_Meta_matchesInstance(
        v_e_3106_,
        v_inst_3107_,
        v_a_3108_,
        v_a_3109_,
        v_a_3110_,
        v_a_3111_,
    );
    lean_dec(v_a_3111_);
    lean_dec_ref(v_a_3110_);
    lean_dec(v_a_3109_);
    lean_dec_ref(v_a_3108_);
    return v_res_3113_;
}
pub unsafe fn l_Lean_Meta_isOffset_x3f(
    mut v_e_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
    mut v_a_3117_: *mut LeanObject,
    mut v_a_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v_arg_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: u8 = 0;
    let mut v_arg_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3161_: u8 = 0;
    let mut v_fst_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut v_a_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3182_: u8 = 0;
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_isSharedCheck_3187_: u8 = 0;
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v_a_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3192_: u8 = 0;
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3196_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: u8 = 0;
    let mut v_arg_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3224_: u8 = 0;
    let mut v_a_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3244_: u8 = 0;
    let mut v_a_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v_fst_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_a_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3277_: u8 = 0;
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v_a_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3120_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3114_, v_a_3116_);
                if lean_obj_tag(v___x_3120_) == 0 {
                    v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
                    v_isSharedCheck_3282_ = (!lean_is_exclusive(v___x_3120_)) as u8;
                    if v_isSharedCheck_3282_ == 0 {
                        v___x_3123_ = v___x_3120_;
                        v_isShared_3124_ = v_isSharedCheck_3282_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3121_);
                        lean_dec(v___x_3120_);
                        v___x_3123_ = lean_box(0);
                        v_isShared_3124_ = v_isSharedCheck_3282_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3283_ = lean_ctor_get(v___x_3120_, 0);
                    v_isSharedCheck_3290_ = (!lean_is_exclusive(v___x_3120_)) as u8;
                    if v_isSharedCheck_3290_ == 0 {
                        v___x_3285_ = v___x_3120_;
                        v_isShared_3286_ = v_isSharedCheck_3290_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_3283_);
                        lean_dec(v___x_3120_);
                        v___x_3285_ = lean_box(0);
                        v_isShared_3286_ = v_isSharedCheck_3290_;
                        state = 31;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3130_ = l_Lean_Expr_cleanupAnnotations(v_a_3121_);
                v___x_3131_ = l_Lean_Expr_isApp(v___x_3130_);
                if v___x_3131_ == 0 {
                    lean_dec_ref(v___x_3130_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3132_ = lean_ctor_get(v___x_3130_, 1);
                    lean_inc_ref(v_arg_3132_);
                    v___x_3133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3130_);
                    v___x_3134_ =
                        l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__1;
                    v___x_3135_ = l_Lean_Expr_isConstOf(v___x_3133_, v___x_3134_);
                    if v___x_3135_ == 0 {
                        v___x_3136_ = l_Lean_Expr_isApp(v___x_3133_);
                        if v___x_3136_ == 0 {
                            lean_dec_ref(v___x_3133_);
                            lean_dec_ref(v_arg_3132_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_3137_ = lean_ctor_get(v___x_3133_, 1);
                            lean_inc_ref(v_arg_3137_);
                            v___x_3197_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3133_);
                            v___x_3198_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__13;
                            v___x_3199_ = l_Lean_Expr_isConstOf(v___x_3197_, v___x_3198_);
                            if v___x_3199_ == 0 {
                                v___x_3200_ = l_Lean_Expr_isApp(v___x_3197_);
                                if v___x_3200_ == 0 {
                                    lean_dec_ref(v___x_3197_);
                                    lean_dec_ref(v_arg_3137_);
                                    lean_dec_ref(v_arg_3132_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_3201_ = lean_ctor_get(v___x_3197_, 1);
                                    lean_inc_ref(v_arg_3201_);
                                    v___x_3202_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3197_);
                                    v___x_3203_ = l_Lean_Expr_isApp(v___x_3202_);
                                    if v___x_3203_ == 0 {
                                        lean_dec_ref(v___x_3202_);
                                        lean_dec_ref(v_arg_3201_);
                                        lean_dec_ref(v_arg_3137_);
                                        lean_dec_ref(v_arg_3132_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3204_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3202_);
                                        v___x_3205_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__28;
                                        v___x_3206_ =
                                            l_Lean_Expr_isConstOf(v___x_3204_, v___x_3205_);
                                        if v___x_3206_ == 0 {
                                            v___x_3207_ = l_Lean_Expr_isApp(v___x_3204_);
                                            if v___x_3207_ == 0 {
                                                lean_dec_ref(v___x_3204_);
                                                lean_dec_ref(v_arg_3201_);
                                                lean_dec_ref(v_arg_3137_);
                                                lean_dec_ref(v_arg_3132_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_3208_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_3204_);
                                                v___x_3209_ = l_Lean_Expr_isApp(v___x_3208_);
                                                if v___x_3209_ == 0 {
                                                    lean_dec_ref(v___x_3208_);
                                                    lean_dec_ref(v_arg_3201_);
                                                    lean_dec_ref(v_arg_3137_);
                                                    lean_dec_ref(v_arg_3132_);
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_3210_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_3208_,
                                                    );
                                                    v___x_3211_ = l___private_Lean_Meta_Offset_0__Lean_Meta_evalNat_visit___closed__48;
                                                    v___x_3212_ = l_Lean_Expr_isConstOf(
                                                        v___x_3210_,
                                                        v___x_3211_,
                                                    );
                                                    lean_dec_ref(v___x_3210_);
                                                    if v___x_3212_ == 0 {
                                                        lean_dec_ref(v_arg_3201_);
                                                        lean_dec_ref(v_arg_3137_);
                                                        lean_dec_ref(v_arg_3132_);
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        lean_del_object(v___x_3123_);
                                                        v___x_3213_ = l_Lean_Nat_mkInstHAdd;
                                                        v___x_3214_ = l_Lean_Meta_matchesInstance(
                                                            v_arg_3201_,
                                                            v___x_3213_,
                                                            v_a_3115_,
                                                            v_a_3116_,
                                                            v_a_3117_,
                                                            v_a_3118_,
                                                        );
                                                        if lean_obj_tag(v___x_3214_) == 0 {
                                                            v_a_3215_ =
                                                                lean_ctor_get(v___x_3214_, 0);
                                                            v_isSharedCheck_3224_ =
                                                                (!lean_is_exclusive(v___x_3214_))
                                                                    as u8;
                                                            if v_isSharedCheck_3224_ == 0 {
                                                                v___x_3217_ = v___x_3214_;
                                                                v_isShared_3218_ =
                                                                    v_isSharedCheck_3224_;
                                                                state = 17;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3215_);
                                                                lean_dec(v___x_3214_);
                                                                v___x_3217_ = lean_box(0);
                                                                v_isShared_3218_ =
                                                                    v_isSharedCheck_3224_;
                                                                state = 17;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_3137_);
                                                            lean_dec_ref(v_arg_3132_);
                                                            v_a_3225_ =
                                                                lean_ctor_get(v___x_3214_, 0);
                                                            v_isSharedCheck_3232_ =
                                                                (!lean_is_exclusive(v___x_3214_))
                                                                    as u8;
                                                            if v_isSharedCheck_3232_ == 0 {
                                                                v___x_3227_ = v___x_3214_;
                                                                v_isShared_3228_ =
                                                                    v_isSharedCheck_3232_;
                                                                state = 19;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3225_);
                                                                lean_dec(v___x_3214_);
                                                                v___x_3227_ = lean_box(0);
                                                                v_isShared_3228_ =
                                                                    v_isSharedCheck_3232_;
                                                                state = 19;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_3204_);
                                            lean_del_object(v___x_3123_);
                                            v___x_3233_ = l_Lean_Nat_mkInstAdd;
                                            v___x_3234_ = l_Lean_Meta_matchesInstance(
                                                v_arg_3201_,
                                                v___x_3233_,
                                                v_a_3115_,
                                                v_a_3116_,
                                                v_a_3117_,
                                                v_a_3118_,
                                            );
                                            if lean_obj_tag(v___x_3234_) == 0 {
                                                v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
                                                v_isSharedCheck_3244_ =
                                                    (!lean_is_exclusive(v___x_3234_)) as u8;
                                                if v_isSharedCheck_3244_ == 0 {
                                                    v___x_3237_ = v___x_3234_;
                                                    v_isShared_3238_ = v_isSharedCheck_3244_;
                                                    state = 21;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3235_);
                                                    lean_dec(v___x_3234_);
                                                    v___x_3237_ = lean_box(0);
                                                    v_isShared_3238_ = v_isSharedCheck_3244_;
                                                    state = 21;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_3137_);
                                                lean_dec_ref(v_arg_3132_);
                                                v_a_3245_ = lean_ctor_get(v___x_3234_, 0);
                                                v_isSharedCheck_3252_ =
                                                    (!lean_is_exclusive(v___x_3234_)) as u8;
                                                if v_isSharedCheck_3252_ == 0 {
                                                    v___x_3247_ = v___x_3234_;
                                                    v_isShared_3248_ = v_isSharedCheck_3252_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3245_);
                                                    lean_dec(v___x_3234_);
                                                    v___x_3247_ = lean_box(0);
                                                    v_isShared_3248_ = v_isSharedCheck_3252_;
                                                    state = 23;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_3197_);
                                lean_del_object(v___x_3123_);
                                v_b_3139_ = v_arg_3132_;
                                v___y_3140_ = v_a_3115_;
                                v___y_3141_ = v_a_3116_;
                                v___y_3142_ = v_a_3117_;
                                v___y_3143_ = v_a_3118_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3133_);
                        lean_del_object(v___x_3123_);
                        v___x_3253_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(
                            v_arg_3132_,
                            v_a_3115_,
                            v_a_3116_,
                            v_a_3117_,
                            v_a_3118_,
                        );
                        if lean_obj_tag(v___x_3253_) == 0 {
                            v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
                            v_isSharedCheck_3273_ = (!lean_is_exclusive(v___x_3253_)) as u8;
                            if v_isSharedCheck_3273_ == 0 {
                                v___x_3256_ = v___x_3253_;
                                v_isShared_3257_ = v_isSharedCheck_3273_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_3254_);
                                lean_dec(v___x_3253_);
                                v___x_3256_ = lean_box(0);
                                v_isShared_3257_ = v_isSharedCheck_3273_;
                                state = 25;
                                continue;
                            }
                        } else {
                            v_a_3274_ = lean_ctor_get(v___x_3253_, 0);
                            v_isSharedCheck_3281_ = (!lean_is_exclusive(v___x_3253_)) as u8;
                            if v_isSharedCheck_3281_ == 0 {
                                v___x_3276_ = v___x_3253_;
                                v_isShared_3277_ = v_isSharedCheck_3281_;
                                state = 29;
                                continue;
                            } else {
                                lean_inc(v_a_3274_);
                                lean_dec(v___x_3253_);
                                v___x_3276_ = lean_box(0);
                                v_isShared_3277_ = v_isSharedCheck_3281_;
                                state = 29;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3126_ = lean_box(0);
                if v_isShared_3124_ == 0 {
                    lean_ctor_set(v___x_3123_, 0, v___x_3126_);
                    v___x_3128_ = v___x_3123_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
                    v___x_3128_ = v_reuseFailAlloc_3129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3128_;
            }
            4 => {
                v___x_3144_ = l_Lean_Meta_evalNat(
                    v_b_3139_,
                    v___y_3140_,
                    v___y_3141_,
                    v___y_3142_,
                    v___y_3143_,
                );
                if lean_obj_tag(v___x_3144_) == 0 {
                    v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
                    v_isSharedCheck_3188_ = (!lean_is_exclusive(v___x_3144_)) as u8;
                    if v_isSharedCheck_3188_ == 0 {
                        v___x_3147_ = v___x_3144_;
                        v_isShared_3148_ = v_isSharedCheck_3188_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3145_);
                        lean_dec(v___x_3144_);
                        v___x_3147_ = lean_box(0);
                        v_isShared_3148_ = v_isSharedCheck_3188_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_arg_3137_);
                    v_a_3189_ = lean_ctor_get(v___x_3144_, 0);
                    v_isSharedCheck_3196_ = (!lean_is_exclusive(v___x_3144_)) as u8;
                    if v_isSharedCheck_3196_ == 0 {
                        v___x_3191_ = v___x_3144_;
                        v_isShared_3192_ = v_isSharedCheck_3196_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3189_);
                        lean_dec(v___x_3144_);
                        v___x_3191_ = lean_box(0);
                        v_isShared_3192_ = v_isSharedCheck_3196_;
                        state = 15;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_3145_) == 0 {
                    lean_dec_ref(v_arg_3137_);
                    v___x_3149_ = lean_box(0);
                    if v_isShared_3148_ == 0 {
                        lean_ctor_set(v___x_3147_, 0, v___x_3149_);
                        v___x_3151_ = v___x_3147_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3149_);
                        v___x_3151_ = v_reuseFailAlloc_3152_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3147_);
                    v_val_3153_ = lean_ctor_get(v_a_3145_, 0);
                    v_isSharedCheck_3187_ = (!lean_is_exclusive(v_a_3145_)) as u8;
                    if v_isSharedCheck_3187_ == 0 {
                        v___x_3155_ = v_a_3145_;
                        v_isShared_3156_ = v_isSharedCheck_3187_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_3153_);
                        lean_dec(v_a_3145_);
                        v___x_3155_ = lean_box(0);
                        v_isShared_3156_ = v_isSharedCheck_3187_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3151_;
            }
            7 => {
                v___x_3157_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(
                    v_arg_3137_,
                    v___y_3140_,
                    v___y_3141_,
                    v___y_3142_,
                    v___y_3143_,
                );
                if lean_obj_tag(v___x_3157_) == 0 {
                    v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
                    v_isSharedCheck_3178_ = (!lean_is_exclusive(v___x_3157_)) as u8;
                    if v_isSharedCheck_3178_ == 0 {
                        v___x_3160_ = v___x_3157_;
                        v_isShared_3161_ = v_isSharedCheck_3178_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3158_);
                        lean_dec(v___x_3157_);
                        v___x_3160_ = lean_box(0);
                        v_isShared_3161_ = v_isSharedCheck_3178_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3155_);
                    lean_dec(v_val_3153_);
                    v_a_3179_ = lean_ctor_get(v___x_3157_, 0);
                    v_isSharedCheck_3186_ = (!lean_is_exclusive(v___x_3157_)) as u8;
                    if v_isSharedCheck_3186_ == 0 {
                        v___x_3181_ = v___x_3157_;
                        v_isShared_3182_ = v_isSharedCheck_3186_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3179_);
                        lean_dec(v___x_3157_);
                        v___x_3181_ = lean_box(0);
                        v_isShared_3182_ = v_isSharedCheck_3186_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                v_fst_3162_ = lean_ctor_get(v_a_3158_, 0);
                v_snd_3163_ = lean_ctor_get(v_a_3158_, 1);
                v_isSharedCheck_3177_ = (!lean_is_exclusive(v_a_3158_)) as u8;
                if v_isSharedCheck_3177_ == 0 {
                    v___x_3165_ = v_a_3158_;
                    v_isShared_3166_ = v_isSharedCheck_3177_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_snd_3163_);
                    lean_inc(v_fst_3162_);
                    lean_dec(v_a_3158_);
                    v___x_3165_ = lean_box(0);
                    v_isShared_3166_ = v_isSharedCheck_3177_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3167_ = lean_nat_add(v_snd_3163_, v_val_3153_);
                lean_dec(v_val_3153_);
                lean_dec(v_snd_3163_);
                if v_isShared_3166_ == 0 {
                    lean_ctor_set(v___x_3165_, 1, v___x_3167_);
                    v___x_3169_ = v___x_3165_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_fst_3162_);
                    lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___x_3167_);
                    v___x_3169_ = v_reuseFailAlloc_3176_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3156_ == 0 {
                    lean_ctor_set(v___x_3155_, 0, v___x_3169_);
                    v___x_3171_ = v___x_3155_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3169_);
                    v___x_3171_ = v_reuseFailAlloc_3175_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3161_ == 0 {
                    lean_ctor_set(v___x_3160_, 0, v___x_3171_);
                    v___x_3173_ = v___x_3160_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
                    v___x_3173_ = v_reuseFailAlloc_3174_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3173_;
            }
            13 => {
                if v_isShared_3182_ == 0 {
                    v___x_3184_ = v___x_3181_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
                    v___x_3184_ = v_reuseFailAlloc_3185_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3184_;
            }
            15 => {
                if v_isShared_3192_ == 0 {
                    v___x_3194_ = v___x_3191_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
                    v___x_3194_ = v_reuseFailAlloc_3195_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3194_;
            }
            17 => {
                v___x_3219_ = (lean_unbox(v_a_3215_) as u8);
                lean_dec(v_a_3215_);
                if v___x_3219_ == 0 {
                    lean_dec_ref(v_arg_3137_);
                    lean_dec_ref(v_arg_3132_);
                    v___x_3220_ = lean_box(0);
                    if v_isShared_3218_ == 0 {
                        lean_ctor_set(v___x_3217_, 0, v___x_3220_);
                        v___x_3222_ = v___x_3217_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
                        v___x_3222_ = v_reuseFailAlloc_3223_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3217_);
                    v_b_3139_ = v_arg_3132_;
                    v___y_3140_ = v_a_3115_;
                    v___y_3141_ = v_a_3116_;
                    v___y_3142_ = v_a_3117_;
                    v___y_3143_ = v_a_3118_;
                    state = 4;
                    continue;
                }
            }
            18 => {
                return v___x_3222_;
            }
            19 => {
                if v_isShared_3228_ == 0 {
                    v___x_3230_ = v___x_3227_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3230_;
            }
            21 => {
                v___x_3239_ = (lean_unbox(v_a_3235_) as u8);
                lean_dec(v_a_3235_);
                if v___x_3239_ == 0 {
                    lean_dec_ref(v_arg_3137_);
                    lean_dec_ref(v_arg_3132_);
                    v___x_3240_ = lean_box(0);
                    if v_isShared_3238_ == 0 {
                        lean_ctor_set(v___x_3237_, 0, v___x_3240_);
                        v___x_3242_ = v___x_3237_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
                        v___x_3242_ = v_reuseFailAlloc_3243_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3237_);
                    v_b_3139_ = v_arg_3132_;
                    v___y_3140_ = v_a_3115_;
                    v___y_3141_ = v_a_3116_;
                    v___y_3142_ = v_a_3117_;
                    v___y_3143_ = v_a_3118_;
                    state = 4;
                    continue;
                }
            }
            22 => {
                return v___x_3242_;
            }
            23 => {
                if v_isShared_3248_ == 0 {
                    v___x_3250_ = v___x_3247_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3250_;
            }
            25 => {
                v_fst_3258_ = lean_ctor_get(v_a_3254_, 0);
                v_snd_3259_ = lean_ctor_get(v_a_3254_, 1);
                v_isSharedCheck_3272_ = (!lean_is_exclusive(v_a_3254_)) as u8;
                if v_isSharedCheck_3272_ == 0 {
                    v___x_3261_ = v_a_3254_;
                    v_isShared_3262_ = v_isSharedCheck_3272_;
                    state = 26;
                    continue;
                } else {
                    lean_inc(v_snd_3259_);
                    lean_inc(v_fst_3258_);
                    lean_dec(v_a_3254_);
                    v___x_3261_ = lean_box(0);
                    v_isShared_3262_ = v_isSharedCheck_3272_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_3263_ = lean_unsigned_to_nat(1);
                v___x_3264_ = lean_nat_add(v_snd_3259_, v___x_3263_);
                lean_dec(v_snd_3259_);
                if v_isShared_3262_ == 0 {
                    lean_ctor_set(v___x_3261_, 1, v___x_3264_);
                    v___x_3266_ = v___x_3261_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_fst_3258_);
                    lean_ctor_set(v_reuseFailAlloc_3271_, 1, v___x_3264_);
                    v___x_3266_ = v_reuseFailAlloc_3271_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_3267_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3267_, 0, v___x_3266_);
                if v_isShared_3257_ == 0 {
                    lean_ctor_set(v___x_3256_, 0, v___x_3267_);
                    v___x_3269_ = v___x_3256_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
                    v___x_3269_ = v_reuseFailAlloc_3270_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3269_;
            }
            29 => {
                if v_isShared_3277_ == 0 {
                    v___x_3279_ = v___x_3276_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
                    v___x_3279_ = v_reuseFailAlloc_3280_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3279_;
            }
            31 => {
                if v_isShared_3286_ == 0 {
                    v___x_3288_ = v___x_3285_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(
    mut v_e_3291_: *mut LeanObject,
    mut v_a_3292_: *mut LeanObject,
    mut v_a_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
    mut v_a_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3311_: u8 = 0;
    let mut v_a_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3291_);
                v___x_3297_ =
                    l_Lean_Meta_isOffset_x3f(v_e_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
                if lean_obj_tag(v___x_3297_) == 0 {
                    v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3311_ = (!lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3311_ == 0 {
                        v___x_3300_ = v___x_3297_;
                        v_isShared_3301_ = v_isSharedCheck_3311_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3298_);
                        lean_dec(v___x_3297_);
                        v___x_3300_ = lean_box(0);
                        v_isShared_3301_ = v_isSharedCheck_3311_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3291_);
                    v_a_3312_ = lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3319_ = (!lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3314_ = v___x_3297_;
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3312_);
                        lean_dec(v___x_3297_);
                        v___x_3314_ = lean_box(0);
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3298_) == 0 {
                    v___x_3302_ = lean_unsigned_to_nat(0);
                    v___x_3303_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3303_, 0, v_e_3291_);
                    lean_ctor_set(v___x_3303_, 1, v___x_3302_);
                    if v_isShared_3301_ == 0 {
                        lean_ctor_set(v___x_3300_, 0, v___x_3303_);
                        v___x_3305_ = v___x_3300_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
                        v___x_3305_ = v_reuseFailAlloc_3306_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3291_);
                    v_val_3307_ = lean_ctor_get(v_a_3298_, 0);
                    lean_inc(v_val_3307_);
                    lean_dec_ref_known(v_a_3298_, 1);
                    if v_isShared_3301_ == 0 {
                        lean_ctor_set(v___x_3300_, 0, v_val_3307_);
                        v___x_3309_ = v___x_3300_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_val_3307_);
                        v___x_3309_ = v_reuseFailAlloc_3310_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3305_;
            }
            3 => {
                return v___x_3309_;
            }
            4 => {
                if v_isShared_3315_ == 0 {
                    v___x_3317_ = v___x_3314_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
                    v___x_3317_ = v_reuseFailAlloc_3318_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset___boxed(
    mut v_e_3320_: *mut LeanObject,
    mut v_a_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v_a_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3326_: *mut LeanObject = core::ptr::null_mut();
    v_res_3326_ = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(
        v_e_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_,
    );
    lean_dec(v_a_3324_);
    lean_dec_ref(v_a_3323_);
    lean_dec(v_a_3322_);
    lean_dec_ref(v_a_3321_);
    return v_res_3326_;
}
pub unsafe fn l_Lean_Meta_isOffset_x3f___boxed(
    mut v_e_3327_: *mut LeanObject,
    mut v_a_3328_: *mut LeanObject,
    mut v_a_3329_: *mut LeanObject,
    mut v_a_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3333_: *mut LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_Meta_isOffset_x3f(v_e_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
    lean_dec(v_a_3331_);
    lean_dec_ref(v_a_3330_);
    lean_dec(v_a_3329_);
    lean_dec_ref(v_a_3328_);
    return v_res_3333_;
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(
    mut v_e_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
    mut v_a_3338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v_val_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut v_a_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3340_ =
                    l_Lean_Meta_evalNat(v_e_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
                if lean_obj_tag(v___x_3340_) == 0 {
                    v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
                    v_isSharedCheck_3357_ = (!lean_is_exclusive(v___x_3340_)) as u8;
                    if v_isSharedCheck_3357_ == 0 {
                        v___x_3343_ = v___x_3340_;
                        v_isShared_3344_ = v_isSharedCheck_3357_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3341_);
                        lean_dec(v___x_3340_);
                        v___x_3343_ = lean_box(0);
                        v_isShared_3344_ = v_isSharedCheck_3357_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3358_ = lean_ctor_get(v___x_3340_, 0);
                    v_isSharedCheck_3365_ = (!lean_is_exclusive(v___x_3340_)) as u8;
                    if v_isSharedCheck_3365_ == 0 {
                        v___x_3360_ = v___x_3340_;
                        v_isShared_3361_ = v_isSharedCheck_3365_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3358_);
                        lean_dec(v___x_3340_);
                        v___x_3360_ = lean_box(0);
                        v_isShared_3361_ = v_isSharedCheck_3365_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3341_) == 1 {
                    v_val_3345_ = lean_ctor_get(v_a_3341_, 0);
                    lean_inc(v_val_3345_);
                    lean_dec_ref_known(v_a_3341_, 1);
                    v___x_3346_ = lean_unsigned_to_nat(0);
                    v___x_3347_ = lean_nat_dec_eq(v_val_3345_, v___x_3346_);
                    lean_dec(v_val_3345_);
                    v___x_3348_ = lean_box((v___x_3347_) as usize);
                    if v_isShared_3344_ == 0 {
                        lean_ctor_set(v___x_3343_, 0, v___x_3348_);
                        v___x_3350_ = v___x_3343_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
                        v___x_3350_ = v_reuseFailAlloc_3351_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3341_);
                    v___x_3352_ = 0;
                    v___x_3353_ = lean_box((v___x_3352_) as usize);
                    if v_isShared_3344_ == 0 {
                        lean_ctor_set(v___x_3343_, 0, v___x_3353_);
                        v___x_3355_ = v___x_3343_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
                        v___x_3355_ = v_reuseFailAlloc_3356_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3350_;
            }
            3 => {
                return v___x_3355_;
            }
            4 => {
                if v_isShared_3361_ == 0 {
                    v___x_3363_ = v___x_3360_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
                    v___x_3363_ = v_reuseFailAlloc_3364_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(
    mut v_e_3366_: *mut LeanObject,
    mut v_a_3367_: *mut LeanObject,
    mut v_a_3368_: *mut LeanObject,
    mut v_a_3369_: *mut LeanObject,
    mut v_a_3370_: *mut LeanObject,
    mut v_a_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3372_: *mut LeanObject = core::ptr::null_mut();
    v_res_3372_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(
        v_e_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_,
    );
    lean_dec(v_a_3370_);
    lean_dec_ref(v_a_3369_);
    lean_dec(v_a_3368_);
    lean_dec_ref(v_a_3367_);
    return v_res_3372_;
}
pub unsafe fn l_Lean_Meta_mkOffset(
    mut v_e_3373_: *mut LeanObject,
    mut v_offset_3374_: *mut LeanObject,
    mut v_a_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3386_: u8 = 0;
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut v_a_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3380_ = lean_unsigned_to_nat(0);
                v___x_3381_ = lean_nat_dec_eq(v_offset_3374_, v___x_3380_);
                if v___x_3381_ == 0 {
                    lean_inc_ref(v_e_3373_);
                    v___x_3382_ = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(
                        v_e_3373_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_,
                    );
                    if lean_obj_tag(v___x_3382_) == 0 {
                        v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
                        v_isSharedCheck_3397_ = (!lean_is_exclusive(v___x_3382_)) as u8;
                        if v_isSharedCheck_3397_ == 0 {
                            v___x_3385_ = v___x_3382_;
                            v_isShared_3386_ = v_isSharedCheck_3397_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3383_);
                            lean_dec(v___x_3382_);
                            v___x_3385_ = lean_box(0);
                            v_isShared_3386_ = v_isSharedCheck_3397_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_offset_3374_);
                        lean_dec_ref(v_e_3373_);
                        v_a_3398_ = lean_ctor_get(v___x_3382_, 0);
                        v_isSharedCheck_3405_ = (!lean_is_exclusive(v___x_3382_)) as u8;
                        if v_isSharedCheck_3405_ == 0 {
                            v___x_3400_ = v___x_3382_;
                            v_isShared_3401_ = v_isSharedCheck_3405_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3398_);
                            lean_dec(v___x_3382_);
                            v___x_3400_ = lean_box(0);
                            v_isShared_3401_ = v_isSharedCheck_3405_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_offset_3374_);
                    v___x_3406_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3406_, 0, v_e_3373_);
                    return v___x_3406_;
                }
            }
            1 => {
                v___x_3387_ = (lean_unbox(v_a_3383_) as u8);
                lean_dec(v_a_3383_);
                if v___x_3387_ == 0 {
                    v___x_3388_ = l_Lean_mkNatLit(v_offset_3374_);
                    v___x_3389_ = l_Lean_mkNatAdd(v_e_3373_, v___x_3388_);
                    if v_isShared_3386_ == 0 {
                        lean_ctor_set(v___x_3385_, 0, v___x_3389_);
                        v___x_3391_ = v___x_3385_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
                        v___x_3391_ = v_reuseFailAlloc_3392_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3373_);
                    v___x_3393_ = l_Lean_mkNatLit(v_offset_3374_);
                    if v_isShared_3386_ == 0 {
                        lean_ctor_set(v___x_3385_, 0, v___x_3393_);
                        v___x_3395_ = v___x_3385_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
                        v___x_3395_ = v_reuseFailAlloc_3396_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3391_;
            }
            3 => {
                return v___x_3395_;
            }
            4 => {
                if v_isShared_3401_ == 0 {
                    v___x_3403_ = v___x_3400_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
                    v___x_3403_ = v_reuseFailAlloc_3404_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkOffset___boxed(
    mut v_e_3407_: *mut LeanObject,
    mut v_offset_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v_a_3410_: *mut LeanObject,
    mut v_a_3411_: *mut LeanObject,
    mut v_a_3412_: *mut LeanObject,
    mut v_a_3413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3414_: *mut LeanObject = core::ptr::null_mut();
    v_res_3414_ = l_Lean_Meta_mkOffset(
        v_e_3407_,
        v_offset_3408_,
        v_a_3409_,
        v_a_3410_,
        v_a_3411_,
        v_a_3412_,
    );
    lean_dec(v_a_3412_);
    lean_dec_ref(v_a_3411_);
    lean_dec(v_a_3410_);
    lean_dec_ref(v_a_3409_);
    return v_res_3414_;
}
pub unsafe fn l_Lean_Meta_isDefEqOffset___lam__0(
    mut v_s_3415_: *mut LeanObject,
    mut v_t_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_a_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3422_ = lean_is_expr_def_eq(
                    v_s_3415_,
                    v_t_3416_,
                    v___y_3417_,
                    v___y_3418_,
                    v___y_3419_,
                    v___y_3420_,
                );
                if lean_obj_tag(v___x_3422_) == 0 {
                    v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
                    v_isSharedCheck_3433_ = (!lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3433_ == 0 {
                        v___x_3425_ = v___x_3422_;
                        v_isShared_3426_ = v_isSharedCheck_3433_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3423_);
                        lean_dec(v___x_3422_);
                        v___x_3425_ = lean_box(0);
                        v_isShared_3426_ = v_isSharedCheck_3433_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3434_ = lean_ctor_get(v___x_3422_, 0);
                    v_isSharedCheck_3441_ = (!lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3441_ == 0 {
                        v___x_3436_ = v___x_3422_;
                        v_isShared_3437_ = v_isSharedCheck_3441_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3434_);
                        lean_dec(v___x_3422_);
                        v___x_3436_ = lean_box(0);
                        v_isShared_3437_ = v_isSharedCheck_3441_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3427_ = (lean_unbox(v_a_3423_) as u8);
                lean_dec(v_a_3423_);
                v___x_3428_ = l_Bool_toLBool(v___x_3427_);
                v___x_3429_ = lean_box((v___x_3428_) as usize);
                if v_isShared_3426_ == 0 {
                    lean_ctor_set(v___x_3425_, 0, v___x_3429_);
                    v___x_3431_ = v___x_3425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
                    v___x_3431_ = v_reuseFailAlloc_3432_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3431_;
            }
            3 => {
                if v_isShared_3437_ == 0 {
                    v___x_3439_ = v___x_3436_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
                    v___x_3439_ = v_reuseFailAlloc_3440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isDefEqOffset___lam__0___boxed(
    mut v_s_3442_: *mut LeanObject,
    mut v_t_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
    mut v___y_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3449_: *mut LeanObject = core::ptr::null_mut();
    v_res_3449_ = l_Lean_Meta_isDefEqOffset___lam__0(
        v_s_3442_,
        v_t_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
        v___y_3447_,
    );
    return v_res_3449_;
}
pub unsafe fn l_Lean_Meta_isDefEqOffset___lam__1(
    mut v___x_3450_: u8,
    mut v___y_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    v___x_3456_ = lean_box((v___x_3450_) as usize);
    v___x_3457_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3457_, 0, v___x_3456_);
    return v___x_3457_;
}
pub unsafe fn l_Lean_Meta_isDefEqOffset___lam__1___boxed(
    mut v___x_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
    mut v___y_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3572__boxed_3464_: u8 = 0;
    let mut v_res_3465_: *mut LeanObject = core::ptr::null_mut();
    v___x_3572__boxed_3464_ = (lean_unbox(v___x_3458_) as u8);
    v_res_3465_ = l_Lean_Meta_isDefEqOffset___lam__1(
        v___x_3572__boxed_3464_,
        v___y_3459_,
        v___y_3460_,
        v___y_3461_,
        v___y_3462_,
    );
    lean_dec(v___y_3462_);
    lean_dec_ref(v___y_3461_);
    lean_dec(v___y_3460_);
    lean_dec_ref(v___y_3459_);
    return v_res_3465_;
}
pub unsafe fn _init_l_Lean_Meta_isDefEqOffset___closed__1() -> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    v___x_3468_ = lean_box(0);
    v___x_3469_ = l_Lean_Meta_isDefEqOffset___closed__0;
    v___x_3470_ = l_Lean_mkConst(v___x_3469_, v___x_3468_);
    return v___x_3470_;
}
pub unsafe fn l_Lean_Meta_isDefEqOffset(
    mut v_s_3474_: *mut LeanObject,
    mut v_t_3475_: *mut LeanObject,
    mut v_a_3476_: *mut LeanObject,
    mut v_a_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: u8 = 0;
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3496_: u8 = 0;
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut v_a_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut v_a_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3516_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut v_s_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offsetCnstrs_3530_: u8 = 0;
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3540_: u8 = 0;
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: u8 = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v_a_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3568_: u8 = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_val_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: u8 = 0;
    let mut v___f_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_a_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut v_val_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3606_: u8 = 0;
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v___f_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v_a_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3621_: u8 = 0;
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3625_: u8 = 0;
    let mut v_val_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: u8 = 0;
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut v_a_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3660_: u8 = 0;
    let mut v_a_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3529_ = l_Lean_Meta_Context_config(v_a_3476_);
                v_offsetCnstrs_3530_ = lean_ctor_get_uint8(v___x_3529_, 8 as u32);
                lean_dec_ref(v___x_3529_);
                if v_offsetCnstrs_3530_ == 0 {
                    lean_dec_ref(v_t_3475_);
                    lean_dec_ref(v_s_3474_);
                    v___x_3531_ = 2;
                    v___x_3532_ = lean_box((v___x_3531_) as usize);
                    v___x_3533_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3533_, 0, v___x_3532_);
                    return v___x_3533_;
                } else {
                    lean_inc_ref(v_s_3474_);
                    v___x_3534_ = l_Lean_Meta_isOffset_x3f(
                        v_s_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                    );
                    if lean_obj_tag(v___x_3534_) == 0 {
                        v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
                        lean_inc(v_a_3535_);
                        lean_dec_ref_known(v___x_3534_, 1);
                        if lean_obj_tag(v_a_3535_) == 0 {
                            lean_inc_ref(v_s_3474_);
                            v___x_3536_ = l_Lean_Meta_evalNat(
                                v_s_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                            );
                            if lean_obj_tag(v___x_3536_) == 0 {
                                v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
                                v_isSharedCheck_3588_ = (!lean_is_exclusive(v___x_3536_)) as u8;
                                if v_isSharedCheck_3588_ == 0 {
                                    v___x_3539_ = v___x_3536_;
                                    v_isShared_3540_ = v_isSharedCheck_3588_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3537_);
                                    lean_dec(v___x_3536_);
                                    v___x_3539_ = lean_box(0);
                                    v_isShared_3540_ = v_isSharedCheck_3588_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_t_3475_);
                                lean_dec_ref(v_s_3474_);
                                v_a_3589_ = lean_ctor_get(v___x_3536_, 0);
                                v_isSharedCheck_3596_ = (!lean_is_exclusive(v___x_3536_)) as u8;
                                if v_isSharedCheck_3596_ == 0 {
                                    v___x_3591_ = v___x_3536_;
                                    v_isShared_3592_ = v_isSharedCheck_3596_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_3589_);
                                    lean_dec(v___x_3536_);
                                    v___x_3591_ = lean_box(0);
                                    v_isShared_3592_ = v_isSharedCheck_3596_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            v_val_3597_ = lean_ctor_get(v_a_3535_, 0);
                            lean_inc(v_val_3597_);
                            lean_dec_ref_known(v_a_3535_, 1);
                            v_fst_3598_ = lean_ctor_get(v_val_3597_, 0);
                            lean_inc(v_fst_3598_);
                            v_snd_3599_ = lean_ctor_get(v_val_3597_, 1);
                            lean_inc(v_snd_3599_);
                            lean_dec(v_val_3597_);
                            lean_inc_ref(v_t_3475_);
                            v___x_3600_ = l_Lean_Meta_isOffset_x3f(
                                v_t_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                            );
                            if lean_obj_tag(v___x_3600_) == 0 {
                                v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
                                lean_inc(v_a_3601_);
                                lean_dec_ref_known(v___x_3600_, 1);
                                if lean_obj_tag(v_a_3601_) == 0 {
                                    v___x_3602_ = l_Lean_Meta_evalNat(
                                        v_t_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                                    );
                                    if lean_obj_tag(v___x_3602_) == 0 {
                                        v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
                                        v_isSharedCheck_3617_ =
                                            (!lean_is_exclusive(v___x_3602_)) as u8;
                                        if v_isSharedCheck_3617_ == 0 {
                                            v___x_3605_ = v___x_3602_;
                                            v_isShared_3606_ = v_isSharedCheck_3617_;
                                            state = 19;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3603_);
                                            lean_dec(v___x_3602_);
                                            v___x_3605_ = lean_box(0);
                                            v_isShared_3606_ = v_isSharedCheck_3617_;
                                            state = 19;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_snd_3599_);
                                        lean_dec(v_fst_3598_);
                                        lean_dec_ref(v_s_3474_);
                                        v_a_3618_ = lean_ctor_get(v___x_3602_, 0);
                                        v_isSharedCheck_3625_ =
                                            (!lean_is_exclusive(v___x_3602_)) as u8;
                                        if v_isSharedCheck_3625_ == 0 {
                                            v___x_3620_ = v___x_3602_;
                                            v_isShared_3621_ = v_isSharedCheck_3625_;
                                            state = 21;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3618_);
                                            lean_dec(v___x_3602_);
                                            v___x_3620_ = lean_box(0);
                                            v_isShared_3621_ = v_isSharedCheck_3625_;
                                            state = 21;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_t_3475_);
                                    v_val_3626_ = lean_ctor_get(v_a_3601_, 0);
                                    lean_inc(v_val_3626_);
                                    lean_dec_ref_known(v_a_3601_, 1);
                                    v_fst_3627_ = lean_ctor_get(v_val_3626_, 0);
                                    lean_inc(v_fst_3627_);
                                    v_snd_3628_ = lean_ctor_get(v_val_3626_, 1);
                                    lean_inc(v_snd_3628_);
                                    lean_dec(v_val_3626_);
                                    v___x_3629_ = lean_nat_dec_eq(v_snd_3599_, v_snd_3628_);
                                    if v___x_3629_ == 0 {
                                        v___x_3630_ = lean_nat_dec_lt(v_snd_3599_, v_snd_3628_);
                                        if v___x_3630_ == 0 {
                                            v___x_3631_ = lean_nat_sub(v_snd_3599_, v_snd_3628_);
                                            lean_dec(v_snd_3628_);
                                            lean_dec(v_snd_3599_);
                                            v___x_3632_ = l_Lean_Meta_mkOffset(
                                                v_fst_3598_,
                                                v___x_3631_,
                                                v_a_3476_,
                                                v_a_3477_,
                                                v_a_3478_,
                                                v_a_3479_,
                                            );
                                            if lean_obj_tag(v___x_3632_) == 0 {
                                                v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
                                                lean_inc(v_a_3633_);
                                                lean_dec_ref_known(v___x_3632_, 1);
                                                v_s_3522_ = v_a_3633_;
                                                v_t_3523_ = v_fst_3627_;
                                                v___y_3524_ = v_a_3476_;
                                                v___y_3525_ = v_a_3477_;
                                                v___y_3526_ = v_a_3478_;
                                                v___y_3527_ = v_a_3479_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_dec(v_fst_3627_);
                                                lean_dec_ref(v_s_3474_);
                                                v_a_3634_ = lean_ctor_get(v___x_3632_, 0);
                                                v_isSharedCheck_3641_ =
                                                    (!lean_is_exclusive(v___x_3632_)) as u8;
                                                if v_isSharedCheck_3641_ == 0 {
                                                    v___x_3636_ = v___x_3632_;
                                                    v_isShared_3637_ = v_isSharedCheck_3641_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3634_);
                                                    lean_dec(v___x_3632_);
                                                    v___x_3636_ = lean_box(0);
                                                    v_isShared_3637_ = v_isSharedCheck_3641_;
                                                    state = 23;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___x_3642_ = lean_nat_sub(v_snd_3628_, v_snd_3599_);
                                            lean_dec(v_snd_3599_);
                                            lean_dec(v_snd_3628_);
                                            v___x_3643_ = l_Lean_Meta_mkOffset(
                                                v_fst_3627_,
                                                v___x_3642_,
                                                v_a_3476_,
                                                v_a_3477_,
                                                v_a_3478_,
                                                v_a_3479_,
                                            );
                                            if lean_obj_tag(v___x_3643_) == 0 {
                                                v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
                                                lean_inc(v_a_3644_);
                                                lean_dec_ref_known(v___x_3643_, 1);
                                                v_s_3522_ = v_fst_3598_;
                                                v_t_3523_ = v_a_3644_;
                                                v___y_3524_ = v_a_3476_;
                                                v___y_3525_ = v_a_3477_;
                                                v___y_3526_ = v_a_3478_;
                                                v___y_3527_ = v_a_3479_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_dec(v_fst_3598_);
                                                lean_dec_ref(v_s_3474_);
                                                v_a_3645_ = lean_ctor_get(v___x_3643_, 0);
                                                v_isSharedCheck_3652_ =
                                                    (!lean_is_exclusive(v___x_3643_)) as u8;
                                                if v_isSharedCheck_3652_ == 0 {
                                                    v___x_3647_ = v___x_3643_;
                                                    v_isShared_3648_ = v_isSharedCheck_3652_;
                                                    state = 25;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3645_);
                                                    lean_dec(v___x_3643_);
                                                    v___x_3647_ = lean_box(0);
                                                    v_isShared_3648_ = v_isSharedCheck_3652_;
                                                    state = 25;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v_snd_3628_);
                                        lean_dec(v_snd_3599_);
                                        v_s_3522_ = v_fst_3598_;
                                        v_t_3523_ = v_fst_3627_;
                                        v___y_3524_ = v_a_3476_;
                                        v___y_3525_ = v_a_3477_;
                                        v___y_3526_ = v_a_3478_;
                                        v___y_3527_ = v_a_3479_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_snd_3599_);
                                lean_dec(v_fst_3598_);
                                lean_dec_ref(v_t_3475_);
                                lean_dec_ref(v_s_3474_);
                                v_a_3653_ = lean_ctor_get(v___x_3600_, 0);
                                v_isSharedCheck_3660_ = (!lean_is_exclusive(v___x_3600_)) as u8;
                                if v_isSharedCheck_3660_ == 0 {
                                    v___x_3655_ = v___x_3600_;
                                    v_isShared_3656_ = v_isSharedCheck_3660_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_inc(v_a_3653_);
                                    lean_dec(v___x_3600_);
                                    v___x_3655_ = lean_box(0);
                                    v_isShared_3656_ = v_isSharedCheck_3660_;
                                    state = 27;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_t_3475_);
                        lean_dec_ref(v_s_3474_);
                        v_a_3661_ = lean_ctor_get(v___x_3534_, 0);
                        v_isSharedCheck_3668_ = (!lean_is_exclusive(v___x_3534_)) as u8;
                        if v_isSharedCheck_3668_ == 0 {
                            v___x_3663_ = v___x_3534_;
                            v_isShared_3664_ = v_isSharedCheck_3668_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_3661_);
                            lean_dec(v___x_3534_);
                            v___x_3663_ = lean_box(0);
                            v_isShared_3664_ = v_isSharedCheck_3668_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v___y_3486_);
                lean_inc_ref(v___y_3485_);
                lean_inc(v___y_3484_);
                lean_inc_ref(v___y_3483_);
                v___x_3487_ = lean_infer_type(
                    v_s_3474_,
                    v___y_3483_,
                    v___y_3484_,
                    v___y_3485_,
                    v___y_3486_,
                );
                if lean_obj_tag(v___x_3487_) == 0 {
                    v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
                    lean_inc(v_a_3488_);
                    lean_dec_ref_known(v___x_3487_, 1);
                    v___x_3489_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_isDefEqOffset___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_isDefEqOffset___closed__1_once),
                        _init_l_Lean_Meta_isDefEqOffset___closed__1,
                    );
                    v___x_3490_ = lean_alloc_closure(
                        l_Lean_Meta_isExprDefEqAux___boxed as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    lean_closure_set(v___x_3490_, 0, v_a_3488_);
                    lean_closure_set(v___x_3490_, 1, v___x_3489_);
                    v___x_3491_ = 0;
                    v___x_3492_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_matchesInstance_spec__0___redArg(v___x_3490_, v___x_3491_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
                    if lean_obj_tag(v___x_3492_) == 0 {
                        v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
                        v_isSharedCheck_3504_ = (!lean_is_exclusive(v___x_3492_)) as u8;
                        if v_isSharedCheck_3504_ == 0 {
                            v___x_3495_ = v___x_3492_;
                            v_isShared_3496_ = v_isSharedCheck_3504_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3493_);
                            lean_dec(v___x_3492_);
                            v___x_3495_ = lean_box(0);
                            v_isShared_3496_ = v_isSharedCheck_3504_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_x_3482_);
                        v_a_3505_ = lean_ctor_get(v___x_3492_, 0);
                        v_isSharedCheck_3512_ = (!lean_is_exclusive(v___x_3492_)) as u8;
                        if v_isSharedCheck_3512_ == 0 {
                            v___x_3507_ = v___x_3492_;
                            v_isShared_3508_ = v_isSharedCheck_3512_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3505_);
                            lean_dec(v___x_3492_);
                            v___x_3507_ = lean_box(0);
                            v_isShared_3508_ = v_isSharedCheck_3512_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_3482_);
                    v_a_3513_ = lean_ctor_get(v___x_3487_, 0);
                    v_isSharedCheck_3520_ = (!lean_is_exclusive(v___x_3487_)) as u8;
                    if v_isSharedCheck_3520_ == 0 {
                        v___x_3515_ = v___x_3487_;
                        v_isShared_3516_ = v_isSharedCheck_3520_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3513_);
                        lean_dec(v___x_3487_);
                        v___x_3515_ = lean_box(0);
                        v_isShared_3516_ = v_isSharedCheck_3520_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3497_ = (lean_unbox(v_a_3493_) as u8);
                lean_dec(v_a_3493_);
                if v___x_3497_ == 0 {
                    lean_dec_ref(v_x_3482_);
                    v___x_3498_ = 2;
                    v___x_3499_ = lean_box((v___x_3498_) as usize);
                    if v_isShared_3496_ == 0 {
                        lean_ctor_set(v___x_3495_, 0, v___x_3499_);
                        v___x_3501_ = v___x_3495_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
                        v___x_3501_ = v_reuseFailAlloc_3502_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3495_);
                    lean_inc(v___y_3486_);
                    lean_inc_ref(v___y_3485_);
                    lean_inc(v___y_3484_);
                    lean_inc_ref(v___y_3483_);
                    v___x_3503_ = lean_apply_5(
                        v_x_3482_,
                        v___y_3483_,
                        v___y_3484_,
                        v___y_3485_,
                        v___y_3486_,
                        lean_box(0),
                    );
                    return v___x_3503_;
                }
            }
            3 => {
                return v___x_3501_;
            }
            4 => {
                if v_isShared_3508_ == 0 {
                    v___x_3510_ = v___x_3507_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
                    v___x_3510_ = v_reuseFailAlloc_3511_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3510_;
            }
            6 => {
                if v_isShared_3516_ == 0 {
                    v___x_3518_ = v___x_3515_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
                    v___x_3518_ = v_reuseFailAlloc_3519_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3518_;
            }
            8 => {
                v___f_3528_ = lean_alloc_closure(
                    l_Lean_Meta_isDefEqOffset___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_3528_, 0, v_s_3522_);
                lean_closure_set(v___f_3528_, 1, v_t_3523_);
                v_x_3482_ = v___f_3528_;
                v___y_3483_ = v___y_3524_;
                v___y_3484_ = v___y_3525_;
                v___y_3485_ = v___y_3526_;
                v___y_3486_ = v___y_3527_;
                state = 1;
                continue;
            }
            9 => {
                if lean_obj_tag(v_a_3537_) == 0 {
                    lean_dec_ref(v_t_3475_);
                    lean_dec_ref(v_s_3474_);
                    v___x_3541_ = 2;
                    v___x_3542_ = lean_box((v___x_3541_) as usize);
                    if v_isShared_3540_ == 0 {
                        lean_ctor_set(v___x_3539_, 0, v___x_3542_);
                        v___x_3544_ = v___x_3539_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
                        v___x_3544_ = v_reuseFailAlloc_3545_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3539_);
                    v_val_3546_ = lean_ctor_get(v_a_3537_, 0);
                    lean_inc(v_val_3546_);
                    lean_dec_ref_known(v_a_3537_, 1);
                    lean_inc_ref(v_t_3475_);
                    v___x_3547_ = l_Lean_Meta_isOffset_x3f(
                        v_t_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                    );
                    if lean_obj_tag(v___x_3547_) == 0 {
                        v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
                        lean_inc(v_a_3548_);
                        lean_dec_ref_known(v___x_3547_, 1);
                        if lean_obj_tag(v_a_3548_) == 0 {
                            v___x_3549_ = l_Lean_Meta_evalNat(
                                v_t_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_,
                            );
                            if lean_obj_tag(v___x_3549_) == 0 {
                                v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
                                v_isSharedCheck_3564_ = (!lean_is_exclusive(v___x_3549_)) as u8;
                                if v_isSharedCheck_3564_ == 0 {
                                    v___x_3552_ = v___x_3549_;
                                    v_isShared_3553_ = v_isSharedCheck_3564_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_3550_);
                                    lean_dec(v___x_3549_);
                                    v___x_3552_ = lean_box(0);
                                    v_isShared_3553_ = v_isSharedCheck_3564_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec(v_val_3546_);
                                lean_dec_ref(v_s_3474_);
                                v_a_3565_ = lean_ctor_get(v___x_3549_, 0);
                                v_isSharedCheck_3572_ = (!lean_is_exclusive(v___x_3549_)) as u8;
                                if v_isSharedCheck_3572_ == 0 {
                                    v___x_3567_ = v___x_3549_;
                                    v_isShared_3568_ = v_isSharedCheck_3572_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_3565_);
                                    lean_dec(v___x_3549_);
                                    v___x_3567_ = lean_box(0);
                                    v_isShared_3568_ = v_isSharedCheck_3572_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_t_3475_);
                            v_val_3573_ = lean_ctor_get(v_a_3548_, 0);
                            lean_inc(v_val_3573_);
                            lean_dec_ref_known(v_a_3548_, 1);
                            v_fst_3574_ = lean_ctor_get(v_val_3573_, 0);
                            lean_inc(v_fst_3574_);
                            v_snd_3575_ = lean_ctor_get(v_val_3573_, 1);
                            lean_inc(v_snd_3575_);
                            lean_dec(v_val_3573_);
                            v___x_3576_ = lean_nat_dec_le(v_snd_3575_, v_val_3546_);
                            if v___x_3576_ == 0 {
                                lean_dec(v_snd_3575_);
                                lean_dec(v_fst_3574_);
                                lean_dec(v_val_3546_);
                                v___f_3577_ = l_Lean_Meta_isDefEqOffset___closed__2;
                                v_x_3482_ = v___f_3577_;
                                v___y_3483_ = v_a_3476_;
                                v___y_3484_ = v_a_3477_;
                                v___y_3485_ = v_a_3478_;
                                v___y_3486_ = v_a_3479_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3578_ = lean_nat_sub(v_val_3546_, v_snd_3575_);
                                lean_dec(v_snd_3575_);
                                lean_dec(v_val_3546_);
                                v___x_3579_ = l_Lean_mkNatLit(v___x_3578_);
                                v_s_3522_ = v___x_3579_;
                                v_t_3523_ = v_fst_3574_;
                                v___y_3524_ = v_a_3476_;
                                v___y_3525_ = v_a_3477_;
                                v___y_3526_ = v_a_3478_;
                                v___y_3527_ = v_a_3479_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3546_);
                        lean_dec_ref(v_t_3475_);
                        lean_dec_ref(v_s_3474_);
                        v_a_3580_ = lean_ctor_get(v___x_3547_, 0);
                        v_isSharedCheck_3587_ = (!lean_is_exclusive(v___x_3547_)) as u8;
                        if v_isSharedCheck_3587_ == 0 {
                            v___x_3582_ = v___x_3547_;
                            v_isShared_3583_ = v_isSharedCheck_3587_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3580_);
                            lean_dec(v___x_3547_);
                            v___x_3582_ = lean_box(0);
                            v_isShared_3583_ = v_isSharedCheck_3587_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            10 => {
                return v___x_3544_;
            }
            11 => {
                if lean_obj_tag(v_a_3550_) == 0 {
                    lean_dec(v_val_3546_);
                    lean_dec_ref(v_s_3474_);
                    v___x_3554_ = 2;
                    v___x_3555_ = lean_box((v___x_3554_) as usize);
                    if v_isShared_3553_ == 0 {
                        lean_ctor_set(v___x_3552_, 0, v___x_3555_);
                        v___x_3557_ = v___x_3552_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
                        v___x_3557_ = v_reuseFailAlloc_3558_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3552_);
                    v_val_3559_ = lean_ctor_get(v_a_3550_, 0);
                    lean_inc(v_val_3559_);
                    lean_dec_ref_known(v_a_3550_, 1);
                    v___x_3560_ = lean_nat_dec_eq(v_val_3546_, v_val_3559_);
                    lean_dec(v_val_3559_);
                    lean_dec(v_val_3546_);
                    v___x_3561_ = l_Bool_toLBool(v___x_3560_);
                    v___x_3562_ = lean_box((v___x_3561_) as usize);
                    v___f_3563_ = lean_alloc_closure(
                        l_Lean_Meta_isDefEqOffset___lam__1___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___f_3563_, 0, v___x_3562_);
                    v_x_3482_ = v___f_3563_;
                    v___y_3483_ = v_a_3476_;
                    v___y_3484_ = v_a_3477_;
                    v___y_3485_ = v_a_3478_;
                    v___y_3486_ = v_a_3479_;
                    state = 1;
                    continue;
                }
            }
            12 => {
                return v___x_3557_;
            }
            13 => {
                if v_isShared_3568_ == 0 {
                    v___x_3570_ = v___x_3567_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
                    v___x_3570_ = v_reuseFailAlloc_3571_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3570_;
            }
            15 => {
                if v_isShared_3583_ == 0 {
                    v___x_3585_ = v___x_3582_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
                    v___x_3585_ = v_reuseFailAlloc_3586_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3585_;
            }
            17 => {
                if v_isShared_3592_ == 0 {
                    v___x_3594_ = v___x_3591_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
                    v___x_3594_ = v_reuseFailAlloc_3595_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3594_;
            }
            19 => {
                if lean_obj_tag(v_a_3603_) == 0 {
                    lean_dec(v_snd_3599_);
                    lean_dec(v_fst_3598_);
                    lean_dec_ref(v_s_3474_);
                    v___x_3607_ = 2;
                    v___x_3608_ = lean_box((v___x_3607_) as usize);
                    if v_isShared_3606_ == 0 {
                        lean_ctor_set(v___x_3605_, 0, v___x_3608_);
                        v___x_3610_ = v___x_3605_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
                        v___x_3610_ = v_reuseFailAlloc_3611_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3605_);
                    v_val_3612_ = lean_ctor_get(v_a_3603_, 0);
                    lean_inc(v_val_3612_);
                    lean_dec_ref_known(v_a_3603_, 1);
                    v___x_3613_ = lean_nat_dec_le(v_snd_3599_, v_val_3612_);
                    if v___x_3613_ == 0 {
                        lean_dec(v_val_3612_);
                        lean_dec(v_snd_3599_);
                        lean_dec(v_fst_3598_);
                        v___f_3614_ = l_Lean_Meta_isDefEqOffset___closed__2;
                        v_x_3482_ = v___f_3614_;
                        v___y_3483_ = v_a_3476_;
                        v___y_3484_ = v_a_3477_;
                        v___y_3485_ = v_a_3478_;
                        v___y_3486_ = v_a_3479_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3615_ = lean_nat_sub(v_val_3612_, v_snd_3599_);
                        lean_dec(v_snd_3599_);
                        lean_dec(v_val_3612_);
                        v___x_3616_ = l_Lean_mkNatLit(v___x_3615_);
                        v_s_3522_ = v_fst_3598_;
                        v_t_3523_ = v___x_3616_;
                        v___y_3524_ = v_a_3476_;
                        v___y_3525_ = v_a_3477_;
                        v___y_3526_ = v_a_3478_;
                        v___y_3527_ = v_a_3479_;
                        state = 8;
                        continue;
                    }
                }
            }
            20 => {
                return v___x_3610_;
            }
            21 => {
                if v_isShared_3621_ == 0 {
                    v___x_3623_ = v___x_3620_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
                    v___x_3623_ = v_reuseFailAlloc_3624_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3623_;
            }
            23 => {
                if v_isShared_3637_ == 0 {
                    v___x_3639_ = v___x_3636_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
                    v___x_3639_ = v_reuseFailAlloc_3640_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3639_;
            }
            25 => {
                if v_isShared_3648_ == 0 {
                    v___x_3650_ = v___x_3647_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
                    v___x_3650_ = v_reuseFailAlloc_3651_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3650_;
            }
            27 => {
                if v_isShared_3656_ == 0 {
                    v___x_3658_ = v___x_3655_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
                    v___x_3658_ = v_reuseFailAlloc_3659_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3658_;
            }
            29 => {
                if v_isShared_3664_ == 0 {
                    v___x_3666_ = v___x_3663_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
                    v___x_3666_ = v_reuseFailAlloc_3667_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isDefEqOffset___boxed(
    mut v_s_3669_: *mut LeanObject,
    mut v_t_3670_: *mut LeanObject,
    mut v_a_3671_: *mut LeanObject,
    mut v_a_3672_: *mut LeanObject,
    mut v_a_3673_: *mut LeanObject,
    mut v_a_3674_: *mut LeanObject,
    mut v_a_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3676_: *mut LeanObject = core::ptr::null_mut();
    v_res_3676_ = l_Lean_Meta_isDefEqOffset(
        v_s_3669_, v_t_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_,
    );
    lean_dec(v_a_3674_);
    lean_dec_ref(v_a_3673_);
    lean_dec(v_a_3672_);
    lean_dec_ref(v_a_3671_);
    return v_res_3676_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Offset(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_LBool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Offset(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Offset(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_LBool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_SafeExponentiation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Offset(builtin);
}

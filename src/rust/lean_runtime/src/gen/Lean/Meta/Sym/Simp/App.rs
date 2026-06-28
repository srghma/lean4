// Lean compiler output
// Module: Lean.Meta.Sym.Simp.App
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Tactic.Simp.Types Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.InferType Lean.Meta.Sym.Simp.CongrInfo Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_bindingBody_x21,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_const___override,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_Expr_isForall, l_Lean_Expr_sort___override, l_Lean_mkApp4,
    l_Lean_mkApp6, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkLambda,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_whnfD;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_getLevel___redArg,
    l_Lean_Meta_Sym_inferType___redArg, l_Lean_Meta_Sym_mkEqRefl___redArg,
    runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::Simp::CongrInfo::{
    initialize_Lean_Meta_Sym_Simp_CongrInfo, l_Lean_Meta_Sym_getCongrInfo___redArg,
    runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_Result_withContextDependent,
    l_Lean_Meta_Sym_Simp_instInhabitedResult_default, l_Lean_Meta_Sym_Simp_instInhabitedSimpM,
    l_Lean_Meta_Sym_Simp_mkRflResultCD, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_instInhabitedSymM, l_Lean_Meta_Sym_isDefEqI___redArg,
    l_Lean_Meta_Sym_shareCommonInc___redArg,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_trySynthInstance;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    initialize_Lean_Meta_Tactic_Simp_Types, l_Lean_Meta_Simp_removeUnnecessaryCasts,
    runtime_initialize_Lean_Meta_Tactic_Simp_Types,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate_rev;
use crate::lean_imports_rs::Lean::Meta::Sym::Simp::SimpM::lean_sym_simp;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_10, lean_apply_11, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0_value)
                as *mut LeanObject,
            2642306550782628284 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [99, 111, 110, 103, 114, 70, 117, 110, 39, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2_value)
                as *mut LeanObject,
            13901408594950942683 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4_value)
                as *mut LeanObject,
            11699215918282396216 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 70, 117, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0_value) as *mut LeanObject,10988039791356833343 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2_value: LeanStringObject<52> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 98, 117, 105, 108, 100, 32, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 112, 114, 111, 111, 102, 44, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1_value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 115, 105, 109, 112, 79, 118, 101, 114, 65, 112, 112, 108, 105, 101, 100, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0_value: LeanStringObject<80> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 112, 114, 111, 112, 97, 103, 97, 116, 101, 79, 118, 101, 114, 65, 112, 112, 108, 105, 101, 100, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [102, 117, 110, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0_value:
    LeanStringObject<63> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83,
        121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77,
        101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 103, 101, 116, 70, 110, 84, 121,
        112, 101, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__0_value) as *mut LeanObject,17542774118954891045 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3_value: LeanStringObject<72> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 115, 105, 109, 112, 70, 105, 120, 101, 100, 80, 114, 101, 102, 105, 120, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0_value: LeanStringObject<71> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 115, 105, 109, 112, 73, 110, 116, 101, 114, 108, 97, 99, 101, 100, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0_value: LeanStringObject<82> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 115, 105, 109, 112, 85, 115, 105, 110, 103, 67, 111, 110, 103, 114, 84, 104, 109, 46, 115, 105, 109, 112, 69, 113, 65, 114, 103, 115, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0_value: LeanStringObject<71> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 115, 105, 109, 112, 85, 115, 105, 110, 103, 67, 111, 110, 103, 114, 84, 104, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__3_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0_value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 115, 105, 109, 112, 65, 112, 112, 65, 114, 103, 82, 97, 110, 103, 101, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46,
            115, 105, 109, 112, 65, 112, 112, 65, 114, 103, 82, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 115, 116, 97, 114, 116, 32, 60, 32, 115, 116, 111, 112, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(
    mut v_f_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
    mut v___y_2444_: *mut LeanObject,
    mut v___y_2445_: *mut LeanObject,
    mut v___y_2446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2459_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut v_a_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2452_ = lean_st_ref_get(v___y_2442_);
                v_debug_2453_ = lean_ctor_get_uint8(
                    v___x_2452_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2452_);
                if v_debug_2453_ == 0 {
                    v___y_2449_ = v___y_2442_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_f_2439_);
                    v___x_2454_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_2439_,
                        v___y_2441_,
                        v___y_2442_,
                        v___y_2443_,
                        v___y_2444_,
                        v___y_2445_,
                        v___y_2446_,
                    );
                    if lean_obj_tag(v___x_2454_) == 0 {
                        lean_dec_ref_known(v___x_2454_, 1);
                        lean_inc_ref(v_a_2440_);
                        v___x_2455_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_2440_,
                            v___y_2441_,
                            v___y_2442_,
                            v___y_2443_,
                            v___y_2444_,
                            v___y_2445_,
                            v___y_2446_,
                        );
                        if lean_obj_tag(v___x_2455_) == 0 {
                            lean_dec_ref_known(v___x_2455_, 1);
                            v___y_2449_ = v___y_2442_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_a_2440_);
                            lean_dec_ref(v_f_2439_);
                            v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
                            v_isSharedCheck_2463_ = (!lean_is_exclusive(v___x_2455_)) as u8;
                            if v_isSharedCheck_2463_ == 0 {
                                v___x_2458_ = v___x_2455_;
                                v_isShared_2459_ = v_isSharedCheck_2463_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2456_);
                                lean_dec(v___x_2455_);
                                v___x_2458_ = lean_box(0);
                                v_isShared_2459_ = v_isSharedCheck_2463_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_a_2440_);
                        lean_dec_ref(v_f_2439_);
                        v_a_2464_ = lean_ctor_get(v___x_2454_, 0);
                        v_isSharedCheck_2471_ = (!lean_is_exclusive(v___x_2454_)) as u8;
                        if v_isSharedCheck_2471_ == 0 {
                            v___x_2466_ = v___x_2454_;
                            v_isShared_2467_ = v_isSharedCheck_2471_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2464_);
                            lean_dec(v___x_2454_);
                            v___x_2466_ = lean_box(0);
                            v_isShared_2467_ = v_isSharedCheck_2471_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2450_ = l_Lean_Expr_app___override(v_f_2439_, v_a_2440_);
                v___x_2451_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2450_, v___y_2449_);
                return v___x_2451_;
            }
            2 => {
                if v_isShared_2459_ == 0 {
                    v___x_2461_ = v___x_2458_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
                    v___x_2461_ = v_reuseFailAlloc_2462_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2461_;
            }
            4 => {
                if v_isShared_2467_ == 0 {
                    v___x_2469_ = v___x_2466_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
                    v___x_2469_ = v_reuseFailAlloc_2470_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(
    mut v_f_2472_: *mut LeanObject,
    mut v_a_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(
        v_f_2472_,
        v_a_2473_,
        v___y_2474_,
        v___y_2475_,
        v___y_2476_,
        v___y_2477_,
        v___y_2478_,
        v___y_2479_,
    );
    lean_dec(v___y_2479_);
    lean_dec_ref(v___y_2478_);
    lean_dec(v___y_2477_);
    lean_dec_ref(v___y_2476_);
    lean_dec(v___y_2475_);
    lean_dec_ref(v___y_2474_);
    return v_res_2481_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(
    mut v_a_2482_: *mut LeanObject,
    mut v_e_2483_: *mut LeanObject,
    mut v_declName_2484_: *mut LeanObject,
    mut v___y_2485_: *mut LeanObject,
    mut v___y_2486_: *mut LeanObject,
    mut v___y_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
    mut v___y_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2511_: u8 = 0;
    let mut v_a_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v_a_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2492_ = l_Lean_Meta_Sym_inferType___redArg(
                    v_a_2482_,
                    v___y_2486_,
                    v___y_2487_,
                    v___y_2488_,
                    v___y_2489_,
                    v___y_2490_,
                );
                if lean_obj_tag(v___x_2492_) == 0 {
                    v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
                    lean_inc_n(v_a_2493_, 2);
                    lean_dec_ref_known(v___x_2492_, 1);
                    v___x_2494_ = l_Lean_Meta_Sym_getLevel___redArg(
                        v_a_2493_,
                        v___y_2486_,
                        v___y_2487_,
                        v___y_2488_,
                        v___y_2489_,
                        v___y_2490_,
                    );
                    if lean_obj_tag(v___x_2494_) == 0 {
                        v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
                        lean_inc(v_a_2495_);
                        lean_dec_ref_known(v___x_2494_, 1);
                        v___x_2496_ = l_Lean_Meta_Sym_inferType___redArg(
                            v_e_2483_,
                            v___y_2486_,
                            v___y_2487_,
                            v___y_2488_,
                            v___y_2489_,
                            v___y_2490_,
                        );
                        if lean_obj_tag(v___x_2496_) == 0 {
                            v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
                            lean_inc_n(v_a_2497_, 2);
                            lean_dec_ref_known(v___x_2496_, 1);
                            v___x_2498_ = l_Lean_Meta_Sym_getLevel___redArg(
                                v_a_2497_,
                                v___y_2486_,
                                v___y_2487_,
                                v___y_2488_,
                                v___y_2489_,
                                v___y_2490_,
                            );
                            if lean_obj_tag(v___x_2498_) == 0 {
                                v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
                                v_isSharedCheck_2511_ = (!lean_is_exclusive(v___x_2498_)) as u8;
                                if v_isSharedCheck_2511_ == 0 {
                                    v___x_2501_ = v___x_2498_;
                                    v_isShared_2502_ = v_isSharedCheck_2511_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2499_);
                                    lean_dec(v___x_2498_);
                                    v___x_2501_ = lean_box(0);
                                    v_isShared_2502_ = v_isSharedCheck_2511_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_2497_);
                                lean_dec(v_a_2495_);
                                lean_dec(v_a_2493_);
                                lean_dec(v_declName_2484_);
                                v_a_2512_ = lean_ctor_get(v___x_2498_, 0);
                                v_isSharedCheck_2519_ = (!lean_is_exclusive(v___x_2498_)) as u8;
                                if v_isSharedCheck_2519_ == 0 {
                                    v___x_2514_ = v___x_2498_;
                                    v_isShared_2515_ = v_isSharedCheck_2519_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2512_);
                                    lean_dec(v___x_2498_);
                                    v___x_2514_ = lean_box(0);
                                    v_isShared_2515_ = v_isSharedCheck_2519_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2495_);
                            lean_dec(v_a_2493_);
                            lean_dec(v_declName_2484_);
                            return v___x_2496_;
                        }
                    } else {
                        lean_dec(v_a_2493_);
                        lean_dec(v_declName_2484_);
                        lean_dec_ref(v_e_2483_);
                        v_a_2520_ = lean_ctor_get(v___x_2494_, 0);
                        v_isSharedCheck_2527_ = (!lean_is_exclusive(v___x_2494_)) as u8;
                        if v_isSharedCheck_2527_ == 0 {
                            v___x_2522_ = v___x_2494_;
                            v_isShared_2523_ = v_isSharedCheck_2527_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2520_);
                            lean_dec(v___x_2494_);
                            v___x_2522_ = lean_box(0);
                            v_isShared_2523_ = v_isSharedCheck_2527_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_2484_);
                    lean_dec_ref(v_e_2483_);
                    return v___x_2492_;
                }
            }
            1 => {
                v___x_2503_ = lean_box(0);
                v___x_2504_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2504_, 0, v_a_2499_);
                lean_ctor_set(v___x_2504_, 1, v___x_2503_);
                v___x_2505_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2505_, 0, v_a_2495_);
                lean_ctor_set(v___x_2505_, 1, v___x_2504_);
                v___x_2506_ = l_Lean_mkConst(v_declName_2484_, v___x_2505_);
                v___x_2507_ = l_Lean_mkAppB(v___x_2506_, v_a_2493_, v_a_2497_);
                if v_isShared_2502_ == 0 {
                    lean_ctor_set(v___x_2501_, 0, v___x_2507_);
                    v___x_2509_ = v___x_2501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
                    v___x_2509_ = v_reuseFailAlloc_2510_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2509_;
            }
            3 => {
                if v_isShared_2515_ == 0 {
                    v___x_2517_ = v___x_2514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
                    v___x_2517_ = v_reuseFailAlloc_2518_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2517_;
            }
            5 => {
                if v_isShared_2523_ == 0 {
                    v___x_2525_ = v___x_2522_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
                    v___x_2525_ = v_reuseFailAlloc_2526_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(
    mut v_a_2528_: *mut LeanObject,
    mut v_e_2529_: *mut LeanObject,
    mut v_declName_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
    mut v___y_2536_: *mut LeanObject,
    mut v___y_2537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2538_: *mut LeanObject = core::ptr::null_mut();
    v_res_2538_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(
        v_a_2528_,
        v_e_2529_,
        v_declName_2530_,
        v___y_2531_,
        v___y_2532_,
        v___y_2533_,
        v___y_2534_,
        v___y_2535_,
        v___y_2536_,
    );
    lean_dec(v___y_2536_);
    lean_dec_ref(v___y_2535_);
    lean_dec(v___y_2534_);
    lean_dec_ref(v___y_2533_);
    lean_dec(v___y_2532_);
    lean_dec_ref(v___y_2531_);
    return v_res_2538_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkCongr___redArg(
    mut v_e_2548_: *mut LeanObject,
    mut v_f_2549_: *mut LeanObject,
    mut v_a_2550_: *mut LeanObject,
    mut v_fr_2551_: *mut LeanObject,
    mut v_ar_2552_: *mut LeanObject,
    mut v_a_2553_: *mut LeanObject,
    mut v_a_2554_: *mut LeanObject,
    mut v_a_2555_: *mut LeanObject,
    mut v_a_2556_: *mut LeanObject,
    mut v_a_2557_: *mut LeanObject,
    mut v_a_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2561_: u8 = 0;
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2564_: u8 = 0;
    let mut v_contextDependent_2565_: u8 = 0;
    let mut v_contextDependent_2566_: u8 = 0;
    let mut v_e_x27_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2569_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: u8 = 0;
    let mut v___y_2584_: u8 = 0;
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_a_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v_a_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v_isSharedCheck_2608_: u8 = 0;
    let mut v_e_x27_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2611_: u8 = 0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2614_: u8 = 0;
    let mut v_contextDependent_2615_: u8 = 0;
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: u8 = 0;
    let mut v___y_2627_: u8 = 0;
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_a_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2638_: u8 = 0;
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2642_: u8 = 0;
    let mut v_a_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut v_e_x27_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2654_: u8 = 0;
    let mut v_e_x27_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2657_: u8 = 0;
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v___y_2672_: u8 = 0;
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v_a_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut v_a_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_fr_2551_) == 0 {
                    if lean_obj_tag(v_ar_2552_) == 0 {
                        lean_dec_ref(v_a_2550_);
                        lean_dec_ref(v_f_2549_);
                        lean_dec_ref(v_e_2548_);
                        v_contextDependent_2564_ = lean_ctor_get_uint8(v_fr_2551_, 1 as u32);
                        lean_dec_ref_known(v_fr_2551_, 0);
                        if v_contextDependent_2564_ == 0 {
                            v_contextDependent_2565_ = lean_ctor_get_uint8(v_ar_2552_, 1 as u32);
                            lean_dec_ref_known(v_ar_2552_, 0);
                            v___y_2561_ = v_contextDependent_2565_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref_known(v_ar_2552_, 0);
                            v___y_2561_ = v_contextDependent_2564_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_contextDependent_2566_ = lean_ctor_get_uint8(v_fr_2551_, 1 as u32);
                        lean_dec_ref_known(v_fr_2551_, 0);
                        v_e_x27_2567_ = lean_ctor_get(v_ar_2552_, 0);
                        v_proof_2568_ = lean_ctor_get(v_ar_2552_, 1);
                        v_contextDependent_2569_ = lean_ctor_get_uint8(
                            v_ar_2552_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v_isSharedCheck_2608_ = (!lean_is_exclusive(v_ar_2552_)) as u8;
                        if v_isSharedCheck_2608_ == 0 {
                            v___x_2571_ = v_ar_2552_;
                            v_isShared_2572_ = v_isSharedCheck_2608_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_proof_2568_);
                            lean_inc(v_e_x27_2567_);
                            lean_dec(v_ar_2552_);
                            v___x_2571_ = lean_box(0);
                            v_isShared_2572_ = v_isSharedCheck_2608_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_ar_2552_) == 0 {
                        v_e_x27_2609_ = lean_ctor_get(v_fr_2551_, 0);
                        v_proof_2610_ = lean_ctor_get(v_fr_2551_, 1);
                        v_contextDependent_2611_ = lean_ctor_get_uint8(
                            v_fr_2551_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v_isSharedCheck_2651_ = (!lean_is_exclusive(v_fr_2551_)) as u8;
                        if v_isSharedCheck_2651_ == 0 {
                            v___x_2613_ = v_fr_2551_;
                            v_isShared_2614_ = v_isSharedCheck_2651_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_proof_2610_);
                            lean_inc(v_e_x27_2609_);
                            lean_dec(v_fr_2551_);
                            v___x_2613_ = lean_box(0);
                            v_isShared_2614_ = v_isSharedCheck_2651_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v_e_x27_2652_ = lean_ctor_get(v_fr_2551_, 0);
                        lean_inc_ref(v_e_x27_2652_);
                        v_proof_2653_ = lean_ctor_get(v_fr_2551_, 1);
                        lean_inc_ref(v_proof_2653_);
                        v_contextDependent_2654_ = lean_ctor_get_uint8(
                            v_fr_2551_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        lean_dec_ref_known(v_fr_2551_, 2);
                        v_e_x27_2655_ = lean_ctor_get(v_ar_2552_, 0);
                        v_proof_2656_ = lean_ctor_get(v_ar_2552_, 1);
                        v_contextDependent_2657_ = lean_ctor_get_uint8(
                            v_ar_2552_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v_isSharedCheck_2696_ = (!lean_is_exclusive(v_ar_2552_)) as u8;
                        if v_isSharedCheck_2696_ == 0 {
                            v___x_2659_ = v_ar_2552_;
                            v_isShared_2660_ = v_isSharedCheck_2696_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_proof_2656_);
                            lean_inc(v_e_x27_2655_);
                            lean_dec(v_ar_2552_);
                            v___x_2659_ = lean_box(0);
                            v_isShared_2660_ = v_isSharedCheck_2696_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2562_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2561_);
                v___x_2563_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2563_, 0, v___x_2562_);
                return v___x_2563_;
            }
            2 => {
                lean_inc_ref(v_e_x27_2567_);
                lean_inc_ref(v_f_2549_);
                v___x_2573_ =
                    l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(
                        v_f_2549_,
                        v_e_x27_2567_,
                        v_a_2553_,
                        v_a_2554_,
                        v_a_2555_,
                        v_a_2556_,
                        v_a_2557_,
                        v_a_2558_,
                    );
                if lean_obj_tag(v___x_2573_) == 0 {
                    v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
                    lean_inc(v_a_2574_);
                    lean_dec_ref_known(v___x_2573_, 1);
                    v___x_2575_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1;
                    lean_inc_ref(v_a_2550_);
                    v___x_2576_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(
                        v_a_2550_,
                        v_e_2548_,
                        v___x_2575_,
                        v_a_2553_,
                        v_a_2554_,
                        v_a_2555_,
                        v_a_2556_,
                        v_a_2557_,
                        v_a_2558_,
                    );
                    if lean_obj_tag(v___x_2576_) == 0 {
                        v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
                        v_isSharedCheck_2591_ = (!lean_is_exclusive(v___x_2576_)) as u8;
                        if v_isSharedCheck_2591_ == 0 {
                            v___x_2579_ = v___x_2576_;
                            v_isShared_2580_ = v_isSharedCheck_2591_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2577_);
                            lean_dec(v___x_2576_);
                            v___x_2579_ = lean_box(0);
                            v_isShared_2580_ = v_isSharedCheck_2591_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2574_);
                        lean_del_object(v___x_2571_);
                        lean_dec_ref(v_proof_2568_);
                        lean_dec_ref(v_e_x27_2567_);
                        lean_dec_ref(v_a_2550_);
                        lean_dec_ref(v_f_2549_);
                        v_a_2592_ = lean_ctor_get(v___x_2576_, 0);
                        v_isSharedCheck_2599_ = (!lean_is_exclusive(v___x_2576_)) as u8;
                        if v_isSharedCheck_2599_ == 0 {
                            v___x_2594_ = v___x_2576_;
                            v_isShared_2595_ = v_isSharedCheck_2599_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2592_);
                            lean_dec(v___x_2576_);
                            v___x_2594_ = lean_box(0);
                            v_isShared_2595_ = v_isSharedCheck_2599_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2571_);
                    lean_dec_ref(v_proof_2568_);
                    lean_dec_ref(v_e_x27_2567_);
                    lean_dec_ref(v_a_2550_);
                    lean_dec_ref(v_f_2549_);
                    lean_dec_ref(v_e_2548_);
                    v_a_2600_ = lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2607_ = (!lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2607_ == 0 {
                        v___x_2602_ = v___x_2573_;
                        v_isShared_2603_ = v_isSharedCheck_2607_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2600_);
                        lean_dec(v___x_2573_);
                        v___x_2602_ = lean_box(0);
                        v_isShared_2603_ = v_isSharedCheck_2607_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2581_ = l_Lean_mkApp4(
                    v_a_2577_,
                    v_a_2550_,
                    v_e_x27_2567_,
                    v_f_2549_,
                    v_proof_2568_,
                );
                v___x_2582_ = 0;
                if v_contextDependent_2566_ == 0 {
                    v___y_2584_ = v_contextDependent_2569_;
                    state = 4;
                    continue;
                } else {
                    v___y_2584_ = v_contextDependent_2566_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2572_ == 0 {
                    lean_ctor_set(v___x_2571_, 1, v___x_2581_);
                    lean_ctor_set(v___x_2571_, 0, v_a_2574_);
                    v___x_2586_ = v___x_2571_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2574_);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2581_);
                    v___x_2586_ = v_reuseFailAlloc_2590_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(
                    v___x_2586_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2582_,
                );
                lean_ctor_set_uint8(
                    v___x_2586_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2584_,
                );
                if v_isShared_2580_ == 0 {
                    lean_ctor_set(v___x_2579_, 0, v___x_2586_);
                    v___x_2588_ = v___x_2579_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2588_;
            }
            7 => {
                if v_isShared_2595_ == 0 {
                    v___x_2597_ = v___x_2594_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
                    v___x_2597_ = v_reuseFailAlloc_2598_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2597_;
            }
            9 => {
                if v_isShared_2603_ == 0 {
                    v___x_2605_ = v___x_2602_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
                    v___x_2605_ = v_reuseFailAlloc_2606_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2605_;
            }
            11 => {
                v_contextDependent_2615_ = lean_ctor_get_uint8(v_ar_2552_, 1 as u32);
                lean_dec_ref_known(v_ar_2552_, 0);
                lean_inc_ref(v_a_2550_);
                lean_inc_ref(v_e_x27_2609_);
                v___x_2616_ =
                    l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(
                        v_e_x27_2609_,
                        v_a_2550_,
                        v_a_2553_,
                        v_a_2554_,
                        v_a_2555_,
                        v_a_2556_,
                        v_a_2557_,
                        v_a_2558_,
                    );
                if lean_obj_tag(v___x_2616_) == 0 {
                    v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
                    lean_inc(v_a_2617_);
                    lean_dec_ref_known(v___x_2616_, 1);
                    v___x_2618_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3;
                    lean_inc_ref(v_a_2550_);
                    v___x_2619_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(
                        v_a_2550_,
                        v_e_2548_,
                        v___x_2618_,
                        v_a_2553_,
                        v_a_2554_,
                        v_a_2555_,
                        v_a_2556_,
                        v_a_2557_,
                        v_a_2558_,
                    );
                    if lean_obj_tag(v___x_2619_) == 0 {
                        v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
                        v_isSharedCheck_2634_ = (!lean_is_exclusive(v___x_2619_)) as u8;
                        if v_isSharedCheck_2634_ == 0 {
                            v___x_2622_ = v___x_2619_;
                            v_isShared_2623_ = v_isSharedCheck_2634_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2620_);
                            lean_dec(v___x_2619_);
                            v___x_2622_ = lean_box(0);
                            v_isShared_2623_ = v_isSharedCheck_2634_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2617_);
                        lean_del_object(v___x_2613_);
                        lean_dec_ref(v_proof_2610_);
                        lean_dec_ref(v_e_x27_2609_);
                        lean_dec_ref(v_a_2550_);
                        lean_dec_ref(v_f_2549_);
                        v_a_2635_ = lean_ctor_get(v___x_2619_, 0);
                        v_isSharedCheck_2642_ = (!lean_is_exclusive(v___x_2619_)) as u8;
                        if v_isSharedCheck_2642_ == 0 {
                            v___x_2637_ = v___x_2619_;
                            v_isShared_2638_ = v_isSharedCheck_2642_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_2635_);
                            lean_dec(v___x_2619_);
                            v___x_2637_ = lean_box(0);
                            v_isShared_2638_ = v_isSharedCheck_2642_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2613_);
                    lean_dec_ref(v_proof_2610_);
                    lean_dec_ref(v_e_x27_2609_);
                    lean_dec_ref(v_a_2550_);
                    lean_dec_ref(v_f_2549_);
                    lean_dec_ref(v_e_2548_);
                    v_a_2643_ = lean_ctor_get(v___x_2616_, 0);
                    v_isSharedCheck_2650_ = (!lean_is_exclusive(v___x_2616_)) as u8;
                    if v_isSharedCheck_2650_ == 0 {
                        v___x_2645_ = v___x_2616_;
                        v_isShared_2646_ = v_isSharedCheck_2650_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2643_);
                        lean_dec(v___x_2616_);
                        v___x_2645_ = lean_box(0);
                        v_isShared_2646_ = v_isSharedCheck_2650_;
                        state = 18;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2624_ = l_Lean_mkApp4(
                    v_a_2620_,
                    v_f_2549_,
                    v_e_x27_2609_,
                    v_proof_2610_,
                    v_a_2550_,
                );
                v___x_2625_ = 0;
                if v_contextDependent_2611_ == 0 {
                    v___y_2627_ = v_contextDependent_2615_;
                    state = 13;
                    continue;
                } else {
                    v___y_2627_ = v_contextDependent_2611_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2614_ == 0 {
                    lean_ctor_set(v___x_2613_, 1, v___x_2624_);
                    lean_ctor_set(v___x_2613_, 0, v_a_2617_);
                    v___x_2629_ = v___x_2613_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2617_);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 1, v___x_2624_);
                    v___x_2629_ = v_reuseFailAlloc_2633_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                lean_ctor_set_uint8(
                    v___x_2629_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2625_,
                );
                lean_ctor_set_uint8(
                    v___x_2629_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2627_,
                );
                if v_isShared_2623_ == 0 {
                    lean_ctor_set(v___x_2622_, 0, v___x_2629_);
                    v___x_2631_ = v___x_2622_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
                    v___x_2631_ = v_reuseFailAlloc_2632_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2631_;
            }
            16 => {
                if v_isShared_2638_ == 0 {
                    v___x_2640_ = v___x_2637_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
                    v___x_2640_ = v_reuseFailAlloc_2641_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2640_;
            }
            18 => {
                if v_isShared_2646_ == 0 {
                    v___x_2648_ = v___x_2645_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
                    v___x_2648_ = v_reuseFailAlloc_2649_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2648_;
            }
            20 => {
                lean_inc_ref(v_e_x27_2655_);
                lean_inc_ref(v_e_x27_2652_);
                v___x_2661_ =
                    l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(
                        v_e_x27_2652_,
                        v_e_x27_2655_,
                        v_a_2553_,
                        v_a_2554_,
                        v_a_2555_,
                        v_a_2556_,
                        v_a_2557_,
                        v_a_2558_,
                    );
                if lean_obj_tag(v___x_2661_) == 0 {
                    v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
                    lean_inc(v_a_2662_);
                    lean_dec_ref_known(v___x_2661_, 1);
                    v___x_2663_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5;
                    lean_inc_ref(v_a_2550_);
                    v___x_2664_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(
                        v_a_2550_,
                        v_e_2548_,
                        v___x_2663_,
                        v_a_2553_,
                        v_a_2554_,
                        v_a_2555_,
                        v_a_2556_,
                        v_a_2557_,
                        v_a_2558_,
                    );
                    if lean_obj_tag(v___x_2664_) == 0 {
                        v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
                        v_isSharedCheck_2679_ = (!lean_is_exclusive(v___x_2664_)) as u8;
                        if v_isSharedCheck_2679_ == 0 {
                            v___x_2667_ = v___x_2664_;
                            v_isShared_2668_ = v_isSharedCheck_2679_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_2665_);
                            lean_dec(v___x_2664_);
                            v___x_2667_ = lean_box(0);
                            v_isShared_2668_ = v_isSharedCheck_2679_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2662_);
                        lean_del_object(v___x_2659_);
                        lean_dec_ref(v_proof_2656_);
                        lean_dec_ref(v_e_x27_2655_);
                        lean_dec_ref(v_proof_2653_);
                        lean_dec_ref(v_e_x27_2652_);
                        lean_dec_ref(v_a_2550_);
                        lean_dec_ref(v_f_2549_);
                        v_a_2680_ = lean_ctor_get(v___x_2664_, 0);
                        v_isSharedCheck_2687_ = (!lean_is_exclusive(v___x_2664_)) as u8;
                        if v_isSharedCheck_2687_ == 0 {
                            v___x_2682_ = v___x_2664_;
                            v_isShared_2683_ = v_isSharedCheck_2687_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_2680_);
                            lean_dec(v___x_2664_);
                            v___x_2682_ = lean_box(0);
                            v_isShared_2683_ = v_isSharedCheck_2687_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2659_);
                    lean_dec_ref(v_proof_2656_);
                    lean_dec_ref(v_e_x27_2655_);
                    lean_dec_ref(v_proof_2653_);
                    lean_dec_ref(v_e_x27_2652_);
                    lean_dec_ref(v_a_2550_);
                    lean_dec_ref(v_f_2549_);
                    lean_dec_ref(v_e_2548_);
                    v_a_2688_ = lean_ctor_get(v___x_2661_, 0);
                    v_isSharedCheck_2695_ = (!lean_is_exclusive(v___x_2661_)) as u8;
                    if v_isSharedCheck_2695_ == 0 {
                        v___x_2690_ = v___x_2661_;
                        v_isShared_2691_ = v_isSharedCheck_2695_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_2688_);
                        lean_dec(v___x_2661_);
                        v___x_2690_ = lean_box(0);
                        v_isShared_2691_ = v_isSharedCheck_2695_;
                        state = 27;
                        continue;
                    }
                }
            }
            21 => {
                v___x_2669_ = l_Lean_mkApp6(
                    v_a_2665_,
                    v_f_2549_,
                    v_e_x27_2652_,
                    v_a_2550_,
                    v_e_x27_2655_,
                    v_proof_2653_,
                    v_proof_2656_,
                );
                v___x_2670_ = 0;
                if v_contextDependent_2654_ == 0 {
                    v___y_2672_ = v_contextDependent_2657_;
                    state = 22;
                    continue;
                } else {
                    v___y_2672_ = v_contextDependent_2654_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2660_ == 0 {
                    lean_ctor_set(v___x_2659_, 1, v___x_2669_);
                    lean_ctor_set(v___x_2659_, 0, v_a_2662_);
                    v___x_2674_ = v___x_2659_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2662_);
                    lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2669_);
                    v___x_2674_ = v_reuseFailAlloc_2678_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                lean_ctor_set_uint8(
                    v___x_2674_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2670_,
                );
                lean_ctor_set_uint8(
                    v___x_2674_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2672_,
                );
                if v_isShared_2668_ == 0 {
                    lean_ctor_set(v___x_2667_, 0, v___x_2674_);
                    v___x_2676_ = v___x_2667_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
                    v___x_2676_ = v_reuseFailAlloc_2677_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2676_;
            }
            25 => {
                if v_isShared_2683_ == 0 {
                    v___x_2685_ = v___x_2682_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
                    v___x_2685_ = v_reuseFailAlloc_2686_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2685_;
            }
            27 => {
                if v_isShared_2691_ == 0 {
                    v___x_2693_ = v___x_2690_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
                    v___x_2693_ = v_reuseFailAlloc_2694_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(
    mut v_e_2697_: *mut LeanObject,
    mut v_f_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
    mut v_fr_2700_: *mut LeanObject,
    mut v_ar_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
    mut v_a_2703_: *mut LeanObject,
    mut v_a_2704_: *mut LeanObject,
    mut v_a_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2709_: *mut LeanObject = core::ptr::null_mut();
    v_res_2709_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(
        v_e_2697_, v_f_2698_, v_a_2699_, v_fr_2700_, v_ar_2701_, v_a_2702_, v_a_2703_, v_a_2704_,
        v_a_2705_, v_a_2706_, v_a_2707_,
    );
    lean_dec(v_a_2707_);
    lean_dec_ref(v_a_2706_);
    lean_dec(v_a_2705_);
    lean_dec_ref(v_a_2704_);
    lean_dec(v_a_2703_);
    lean_dec_ref(v_a_2702_);
    return v_res_2709_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkCongr(
    mut v_e_2710_: *mut LeanObject,
    mut v_f_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_fr_2713_: *mut LeanObject,
    mut v_ar_2714_: *mut LeanObject,
    mut v_x_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
    mut v_a_2719_: *mut LeanObject,
    mut v_a_2720_: *mut LeanObject,
    mut v_a_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(
        v_e_2710_, v_f_2711_, v_a_2712_, v_fr_2713_, v_ar_2714_, v_a_2716_, v_a_2717_, v_a_2718_,
        v_a_2719_, v_a_2720_, v_a_2721_,
    );
    return v___x_2723_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkCongr___boxed(
    mut v_e_2724_: *mut LeanObject,
    mut v_f_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_fr_2727_: *mut LeanObject,
    mut v_ar_2728_: *mut LeanObject,
    mut v_x_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
    mut v_a_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
    mut v_a_2734_: *mut LeanObject,
    mut v_a_2735_: *mut LeanObject,
    mut v_a_2736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2737_: *mut LeanObject = core::ptr::null_mut();
    v_res_2737_ = l_Lean_Meta_Sym_Simp_mkCongr(
        v_e_2724_, v_f_2725_, v_a_2726_, v_fr_2727_, v_ar_2728_, v_x_2729_, v_a_2730_, v_a_2731_,
        v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_,
    );
    lean_dec(v_a_2735_);
    lean_dec_ref(v_a_2734_);
    lean_dec(v_a_2733_);
    lean_dec_ref(v_a_2732_);
    lean_dec(v_a_2731_);
    lean_dec_ref(v_a_2730_);
    return v_res_2737_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(
    mut v_msgData_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    v___x_2744_ = lean_st_ref_get(v___y_2742_);
    v_env_2745_ = lean_ctor_get(v___x_2744_, 0);
    lean_inc_ref(v_env_2745_);
    lean_dec(v___x_2744_);
    v___x_2746_ = lean_st_ref_get(v___y_2740_);
    v_mctx_2747_ = lean_ctor_get(v___x_2746_, 0);
    lean_inc_ref(v_mctx_2747_);
    lean_dec(v___x_2746_);
    v_lctx_2748_ = lean_ctor_get(v___y_2739_, 2);
    v_options_2749_ = lean_ctor_get(v___y_2741_, 2);
    lean_inc_ref(v_options_2749_);
    lean_inc_ref(v_lctx_2748_);
    v___x_2750_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2750_, 0, v_env_2745_);
    lean_ctor_set(v___x_2750_, 1, v_mctx_2747_);
    lean_ctor_set(v___x_2750_, 2, v_lctx_2748_);
    lean_ctor_set(v___x_2750_, 3, v_options_2749_);
    v___x_2751_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2751_, 0, v___x_2750_);
    lean_ctor_set(v___x_2751_, 1, v_msgData_2738_);
    v___x_2752_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2752_, 0, v___x_2751_);
    return v___x_2752_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(
    mut v_msgData_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2759_: *mut LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msgData_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
    lean_dec(v___y_2757_);
    lean_dec_ref(v___y_2756_);
    lean_dec(v___y_2755_);
    lean_dec_ref(v___y_2754_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(
    mut v_msg_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2766_ = lean_ctor_get(v___y_2763_, 5);
                v___x_2767_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(v_msg_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
                v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
                v_isSharedCheck_2776_ = (!lean_is_exclusive(v___x_2767_)) as u8;
                if v_isSharedCheck_2776_ == 0 {
                    v___x_2770_ = v___x_2767_;
                    v_isShared_2771_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2768_);
                    lean_dec(v___x_2767_);
                    v___x_2770_ = lean_box(0);
                    v_isShared_2771_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2766_);
                v___x_2772_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2772_, 0, v_ref_2766_);
                lean_ctor_set(v___x_2772_, 1, v_a_2768_);
                if v_isShared_2771_ == 0 {
                    lean_ctor_set_tag(v___x_2770_, 1);
                    lean_ctor_set(v___x_2770_, 0, v___x_2772_);
                    v___x_2774_ = v___x_2770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
                    v___x_2774_ = v_reuseFailAlloc_2775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(
    mut v_msg_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
    mut v___y_2780_: *mut LeanObject,
    mut v___y_2781_: *mut LeanObject,
    mut v___y_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_res_2783_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
    lean_dec(v___y_2781_);
    lean_dec_ref(v___y_2780_);
    lean_dec(v___y_2779_);
    lean_dec_ref(v___y_2778_);
    return v_res_2783_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    v___x_2788_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2;
    v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
    return v___x_2789_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(
    mut v_e_2790_: *mut LeanObject,
    mut v_f_2791_: *mut LeanObject,
    mut v_a_2792_: *mut LeanObject,
    mut v_f_x27_2793_: *mut LeanObject,
    mut v_hf_2794_: *mut LeanObject,
    mut v_done_2795_: u8,
    mut v_contextDependent_2796_: u8,
    mut v_a_2797_: *mut LeanObject,
    mut v_a_2798_: *mut LeanObject,
    mut v_a_2799_: *mut LeanObject,
    mut v_a_2800_: *mut LeanObject,
    mut v_a_2801_: *mut LeanObject,
    mut v_a_2802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_a_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut v_a_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2847_: u8 = 0;
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut v_a_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut v_a_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2875_: u8 = 0;
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v_a_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_f_2791_);
                v___x_2804_ = l_Lean_Meta_Sym_inferType___redArg(
                    v_f_2791_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_,
                );
                if lean_obj_tag(v___x_2804_) == 0 {
                    v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
                    lean_inc(v_a_2805_);
                    lean_dec_ref_known(v___x_2804_, 1);
                    v___x_2806_ =
                        l_Lean_Meta_whnfD(v_a_2805_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
                    if lean_obj_tag(v___x_2806_) == 0 {
                        v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
                        lean_inc(v_a_2807_);
                        lean_dec_ref_known(v___x_2806_, 1);
                        if lean_obj_tag(v_a_2807_) == 7 {
                            v_binderName_2808_ = lean_ctor_get(v_a_2807_, 0);
                            lean_inc(v_binderName_2808_);
                            v_body_2809_ = lean_ctor_get(v_a_2807_, 2);
                            lean_inc_ref(v_body_2809_);
                            lean_dec_ref_known(v_a_2807_, 3);
                            lean_inc_ref(v_a_2792_);
                            v___x_2810_ = l_Lean_Meta_Sym_inferType___redArg(
                                v_a_2792_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_,
                            );
                            if lean_obj_tag(v___x_2810_) == 0 {
                                v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
                                lean_inc_n(v_a_2811_, 2);
                                lean_dec_ref_known(v___x_2810_, 1);
                                v___x_2812_ = l_Lean_Meta_Sym_getLevel___redArg(
                                    v_a_2811_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_,
                                    v_a_2802_,
                                );
                                if lean_obj_tag(v___x_2812_) == 0 {
                                    v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
                                    lean_inc(v_a_2813_);
                                    lean_dec_ref_known(v___x_2812_, 1);
                                    v___x_2814_ = l_Lean_Meta_Sym_inferType___redArg(
                                        v_e_2790_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_,
                                        v_a_2802_,
                                    );
                                    if lean_obj_tag(v___x_2814_) == 0 {
                                        v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
                                        lean_inc(v_a_2815_);
                                        lean_dec_ref_known(v___x_2814_, 1);
                                        v___x_2816_ = l_Lean_Meta_Sym_getLevel___redArg(
                                            v_a_2815_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_,
                                            v_a_2802_,
                                        );
                                        if lean_obj_tag(v___x_2816_) == 0 {
                                            v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
                                            lean_inc(v_a_2817_);
                                            lean_dec_ref_known(v___x_2816_, 1);
                                            lean_inc_ref(v_a_2792_);
                                            lean_inc_ref(v_f_x27_2793_);
                                            v___x_2818_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Simp_mkCongr_spec__0(v_f_x27_2793_, v_a_2792_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
                                            if lean_obj_tag(v___x_2818_) == 0 {
                                                v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
                                                v_isSharedCheck_2835_ =
                                                    (!lean_is_exclusive(v___x_2818_)) as u8;
                                                if v_isSharedCheck_2835_ == 0 {
                                                    v___x_2821_ = v___x_2818_;
                                                    v_isShared_2822_ = v_isSharedCheck_2835_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2819_);
                                                    lean_dec(v___x_2818_);
                                                    v___x_2821_ = lean_box(0);
                                                    v_isShared_2822_ = v_isSharedCheck_2835_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_a_2817_);
                                                lean_dec(v_a_2813_);
                                                lean_dec(v_a_2811_);
                                                lean_dec_ref(v_body_2809_);
                                                lean_dec(v_binderName_2808_);
                                                lean_dec_ref(v_hf_2794_);
                                                lean_dec_ref(v_f_x27_2793_);
                                                lean_dec_ref(v_a_2792_);
                                                lean_dec_ref(v_f_2791_);
                                                v_a_2836_ = lean_ctor_get(v___x_2818_, 0);
                                                v_isSharedCheck_2843_ =
                                                    (!lean_is_exclusive(v___x_2818_)) as u8;
                                                if v_isSharedCheck_2843_ == 0 {
                                                    v___x_2838_ = v___x_2818_;
                                                    v_isShared_2839_ = v_isSharedCheck_2843_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2836_);
                                                    lean_dec(v___x_2818_);
                                                    v___x_2838_ = lean_box(0);
                                                    v_isShared_2839_ = v_isSharedCheck_2843_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_2813_);
                                            lean_dec(v_a_2811_);
                                            lean_dec_ref(v_body_2809_);
                                            lean_dec(v_binderName_2808_);
                                            lean_dec_ref(v_hf_2794_);
                                            lean_dec_ref(v_f_x27_2793_);
                                            lean_dec_ref(v_a_2792_);
                                            lean_dec_ref(v_f_2791_);
                                            v_a_2844_ = lean_ctor_get(v___x_2816_, 0);
                                            v_isSharedCheck_2851_ =
                                                (!lean_is_exclusive(v___x_2816_)) as u8;
                                            if v_isSharedCheck_2851_ == 0 {
                                                v___x_2846_ = v___x_2816_;
                                                v_isShared_2847_ = v_isSharedCheck_2851_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2844_);
                                                lean_dec(v___x_2816_);
                                                v___x_2846_ = lean_box(0);
                                                v_isShared_2847_ = v_isSharedCheck_2851_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_2813_);
                                        lean_dec(v_a_2811_);
                                        lean_dec_ref(v_body_2809_);
                                        lean_dec(v_binderName_2808_);
                                        lean_dec_ref(v_hf_2794_);
                                        lean_dec_ref(v_f_x27_2793_);
                                        lean_dec_ref(v_a_2792_);
                                        lean_dec_ref(v_f_2791_);
                                        v_a_2852_ = lean_ctor_get(v___x_2814_, 0);
                                        v_isSharedCheck_2859_ =
                                            (!lean_is_exclusive(v___x_2814_)) as u8;
                                        if v_isSharedCheck_2859_ == 0 {
                                            v___x_2854_ = v___x_2814_;
                                            v_isShared_2855_ = v_isSharedCheck_2859_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2852_);
                                            lean_dec(v___x_2814_);
                                            v___x_2854_ = lean_box(0);
                                            v_isShared_2855_ = v_isSharedCheck_2859_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2811_);
                                    lean_dec_ref(v_body_2809_);
                                    lean_dec(v_binderName_2808_);
                                    lean_dec_ref(v_hf_2794_);
                                    lean_dec_ref(v_f_x27_2793_);
                                    lean_dec_ref(v_a_2792_);
                                    lean_dec_ref(v_f_2791_);
                                    lean_dec_ref(v_e_2790_);
                                    v_a_2860_ = lean_ctor_get(v___x_2812_, 0);
                                    v_isSharedCheck_2867_ = (!lean_is_exclusive(v___x_2812_)) as u8;
                                    if v_isSharedCheck_2867_ == 0 {
                                        v___x_2862_ = v___x_2812_;
                                        v_isShared_2863_ = v_isSharedCheck_2867_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2860_);
                                        lean_dec(v___x_2812_);
                                        v___x_2862_ = lean_box(0);
                                        v_isShared_2863_ = v_isSharedCheck_2867_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_body_2809_);
                                lean_dec(v_binderName_2808_);
                                lean_dec_ref(v_hf_2794_);
                                lean_dec_ref(v_f_x27_2793_);
                                lean_dec_ref(v_a_2792_);
                                lean_dec_ref(v_f_2791_);
                                lean_dec_ref(v_e_2790_);
                                v_a_2868_ = lean_ctor_get(v___x_2810_, 0);
                                v_isSharedCheck_2875_ = (!lean_is_exclusive(v___x_2810_)) as u8;
                                if v_isSharedCheck_2875_ == 0 {
                                    v___x_2870_ = v___x_2810_;
                                    v_isShared_2871_ = v_isSharedCheck_2875_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_2868_);
                                    lean_dec(v___x_2810_);
                                    v___x_2870_ = lean_box(0);
                                    v_isShared_2871_ = v_isSharedCheck_2875_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2807_);
                            lean_dec_ref(v_hf_2794_);
                            lean_dec_ref(v_f_x27_2793_);
                            lean_dec_ref(v_a_2792_);
                            lean_dec_ref(v_e_2790_);
                            v___x_2876_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
                            v___x_2877_ = l_Lean_indentExpr(v_f_2791_);
                            v___x_2878_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2878_, 0, v___x_2876_);
                            lean_ctor_set(v___x_2878_, 1, v___x_2877_);
                            v___x_2879_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_2878_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
                            return v___x_2879_;
                        }
                    } else {
                        lean_dec_ref(v_hf_2794_);
                        lean_dec_ref(v_f_x27_2793_);
                        lean_dec_ref(v_a_2792_);
                        lean_dec_ref(v_f_2791_);
                        lean_dec_ref(v_e_2790_);
                        v_a_2880_ = lean_ctor_get(v___x_2806_, 0);
                        v_isSharedCheck_2887_ = (!lean_is_exclusive(v___x_2806_)) as u8;
                        if v_isSharedCheck_2887_ == 0 {
                            v___x_2882_ = v___x_2806_;
                            v_isShared_2883_ = v_isSharedCheck_2887_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_2880_);
                            lean_dec(v___x_2806_);
                            v___x_2882_ = lean_box(0);
                            v_isShared_2883_ = v_isSharedCheck_2887_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_hf_2794_);
                    lean_dec_ref(v_f_x27_2793_);
                    lean_dec_ref(v_a_2792_);
                    lean_dec_ref(v_f_2791_);
                    lean_dec_ref(v_e_2790_);
                    v_a_2888_ = lean_ctor_get(v___x_2804_, 0);
                    v_isSharedCheck_2895_ = (!lean_is_exclusive(v___x_2804_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2890_ = v___x_2804_;
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2888_);
                        lean_dec(v___x_2804_);
                        v___x_2890_ = lean_box(0);
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2823_ = 0;
                lean_inc(v_a_2811_);
                v___x_2824_ =
                    l_Lean_mkLambda(v_binderName_2808_, v___x_2823_, v_a_2811_, v_body_2809_);
                v___x_2825_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1;
                v___x_2826_ = lean_box(0);
                v___x_2827_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2827_, 0, v_a_2817_);
                lean_ctor_set(v___x_2827_, 1, v___x_2826_);
                v___x_2828_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2828_, 0, v_a_2813_);
                lean_ctor_set(v___x_2828_, 1, v___x_2827_);
                v___x_2829_ = l_Lean_mkConst(v___x_2825_, v___x_2828_);
                v___x_2830_ = l_Lean_mkApp6(
                    v___x_2829_,
                    v_a_2811_,
                    v___x_2824_,
                    v_f_2791_,
                    v_f_x27_2793_,
                    v_hf_2794_,
                    v_a_2792_,
                );
                v___x_2831_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_2831_, 0, v_a_2819_);
                lean_ctor_set(v___x_2831_, 1, v___x_2830_);
                lean_ctor_set_uint8(
                    v___x_2831_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_done_2795_,
                );
                lean_ctor_set_uint8(
                    v___x_2831_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_2796_,
                );
                if v_isShared_2822_ == 0 {
                    lean_ctor_set(v___x_2821_, 0, v___x_2831_);
                    v___x_2833_ = v___x_2821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
                    v___x_2833_ = v_reuseFailAlloc_2834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2833_;
            }
            3 => {
                if v_isShared_2839_ == 0 {
                    v___x_2841_ = v___x_2838_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
                    v___x_2841_ = v_reuseFailAlloc_2842_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2841_;
            }
            5 => {
                if v_isShared_2847_ == 0 {
                    v___x_2849_ = v___x_2846_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
                    v___x_2849_ = v_reuseFailAlloc_2850_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2849_;
            }
            7 => {
                if v_isShared_2855_ == 0 {
                    v___x_2857_ = v___x_2854_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
                    v___x_2857_ = v_reuseFailAlloc_2858_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2857_;
            }
            9 => {
                if v_isShared_2863_ == 0 {
                    v___x_2865_ = v___x_2862_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
                    v___x_2865_ = v_reuseFailAlloc_2866_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2865_;
            }
            11 => {
                if v_isShared_2871_ == 0 {
                    v___x_2873_ = v___x_2870_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
                    v___x_2873_ = v_reuseFailAlloc_2874_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2873_;
            }
            13 => {
                if v_isShared_2883_ == 0 {
                    v___x_2885_ = v___x_2882_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
                    v___x_2885_ = v_reuseFailAlloc_2886_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2885_;
            }
            15 => {
                if v_isShared_2891_ == 0 {
                    v___x_2893_ = v___x_2890_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
                    v___x_2893_ = v_reuseFailAlloc_2894_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(
    mut v_e_2896_: *mut LeanObject,
    mut v_f_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
    mut v_f_x27_2899_: *mut LeanObject,
    mut v_hf_2900_: *mut LeanObject,
    mut v_done_2901_: *mut LeanObject,
    mut v_contextDependent_2902_: *mut LeanObject,
    mut v_a_2903_: *mut LeanObject,
    mut v_a_2904_: *mut LeanObject,
    mut v_a_2905_: *mut LeanObject,
    mut v_a_2906_: *mut LeanObject,
    mut v_a_2907_: *mut LeanObject,
    mut v_a_2908_: *mut LeanObject,
    mut v_a_2909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_done_boxed_2910_: u8 = 0;
    let mut v_contextDependent_boxed_2911_: u8 = 0;
    let mut v_res_2912_: *mut LeanObject = core::ptr::null_mut();
    v_done_boxed_2910_ = (lean_unbox(v_done_2901_) as u8);
    v_contextDependent_boxed_2911_ = (lean_unbox(v_contextDependent_2902_) as u8);
    v_res_2912_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(
        v_e_2896_,
        v_f_2897_,
        v_a_2898_,
        v_f_x27_2899_,
        v_hf_2900_,
        v_done_boxed_2910_,
        v_contextDependent_boxed_2911_,
        v_a_2903_,
        v_a_2904_,
        v_a_2905_,
        v_a_2906_,
        v_a_2907_,
        v_a_2908_,
    );
    lean_dec(v_a_2908_);
    lean_dec_ref(v_a_2907_);
    lean_dec(v_a_2906_);
    lean_dec_ref(v_a_2905_);
    lean_dec(v_a_2904_);
    lean_dec_ref(v_a_2903_);
    return v_res_2912_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(
    mut v_e_2913_: *mut LeanObject,
    mut v_f_2914_: *mut LeanObject,
    mut v_a_2915_: *mut LeanObject,
    mut v_f_x27_2916_: *mut LeanObject,
    mut v_hf_2917_: *mut LeanObject,
    mut v_x_2918_: *mut LeanObject,
    mut v_done_2919_: u8,
    mut v_contextDependent_2920_: u8,
    mut v_a_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
    mut v_a_2926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    v___x_2928_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(
        v_e_2913_,
        v_f_2914_,
        v_a_2915_,
        v_f_x27_2916_,
        v_hf_2917_,
        v_done_2919_,
        v_contextDependent_2920_,
        v_a_2921_,
        v_a_2922_,
        v_a_2923_,
        v_a_2924_,
        v_a_2925_,
        v_a_2926_,
    );
    return v___x_2928_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(
    mut v_e_2929_: *mut LeanObject,
    mut v_f_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_f_x27_2932_: *mut LeanObject,
    mut v_hf_2933_: *mut LeanObject,
    mut v_x_2934_: *mut LeanObject,
    mut v_done_2935_: *mut LeanObject,
    mut v_contextDependent_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_done_boxed_2944_: u8 = 0;
    let mut v_contextDependent_boxed_2945_: u8 = 0;
    let mut v_res_2946_: *mut LeanObject = core::ptr::null_mut();
    v_done_boxed_2944_ = (lean_unbox(v_done_2935_) as u8);
    v_contextDependent_boxed_2945_ = (lean_unbox(v_contextDependent_2936_) as u8);
    v_res_2946_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun(
        v_e_2929_,
        v_f_2930_,
        v_a_2931_,
        v_f_x27_2932_,
        v_hf_2933_,
        v_x_2934_,
        v_done_boxed_2944_,
        v_contextDependent_boxed_2945_,
        v_a_2937_,
        v_a_2938_,
        v_a_2939_,
        v_a_2940_,
        v_a_2941_,
        v_a_2942_,
    );
    lean_dec(v_a_2942_);
    lean_dec_ref(v_a_2941_);
    lean_dec(v_a_2940_);
    lean_dec_ref(v_a_2939_);
    lean_dec(v_a_2938_);
    lean_dec_ref(v_a_2937_);
    return v_res_2946_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(
    mut v_00_u03b1_2947_: *mut LeanObject,
    mut v_msg_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
    mut v___y_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
    mut v___y_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    v___x_2956_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v_msg_2948_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
    return v___x_2956_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(
    mut v_00_u03b1_2957_: *mut LeanObject,
    mut v_msg_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2966_: *mut LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(v_00_u03b1_2957_, v_msg_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
    lean_dec(v___y_2964_);
    lean_dec_ref(v___y_2963_);
    lean_dec(v___y_2962_);
    lean_dec_ref(v___y_2961_);
    lean_dec(v___y_2960_);
    lean_dec_ref(v___y_2959_);
    return v_res_2966_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    v___x_2967_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
    return v___x_2967_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(
    mut v_msg_2968_: *mut LeanObject,
    mut v___y_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
    mut v___y_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9179__overap_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    v___x_2979_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___closed__0);
    v___x_9179__overap_2980_ = lean_panic_fn_borrowed(v___x_2979_, v_msg_2968_);
    lean_inc(v___y_2977_);
    lean_inc_ref(v___y_2976_);
    lean_inc(v___y_2975_);
    lean_inc_ref(v___y_2974_);
    lean_inc(v___y_2973_);
    lean_inc_ref(v___y_2972_);
    lean_inc(v___y_2971_);
    lean_inc_ref(v___y_2970_);
    lean_inc(v___y_2969_);
    v___x_2981_ = lean_apply_10(
        v___x_9179__overap_2980_,
        v___y_2969_,
        v___y_2970_,
        v___y_2971_,
        v___y_2972_,
        v___y_2973_,
        v___y_2974_,
        v___y_2975_,
        v___y_2976_,
        v___y_2977_,
        lean_box(0),
    );
    return v___x_2981_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0___boxed(
    mut v_msg_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2993_: *mut LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v_msg_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
    lean_dec(v___y_2991_);
    lean_dec_ref(v___y_2990_);
    lean_dec(v___y_2989_);
    lean_dec_ref(v___y_2988_);
    lean_dec(v___y_2987_);
    lean_dec_ref(v___y_2986_);
    lean_dec(v___y_2985_);
    lean_dec_ref(v___y_2984_);
    lean_dec(v___y_2983_);
    return v_res_2993_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3()
-> *mut LeanObject {
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2997_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_2998_ = lean_unsigned_to_nat(55);
    v___x_2999_ = lean_unsigned_to_nat(123);
    v___x_3000_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1;
    v___x_3001_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3002_ = l_mkPanicMessageWithDecl(
        v___x_3001_,
        v___x_3000_,
        v___x_2999_,
        v___x_2998_,
        v___x_2997_,
    );
    return v___x_3002_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4()
-> *mut LeanObject {
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    v___x_3003_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3004_ = lean_unsigned_to_nat(13);
    v___x_3005_ = lean_unsigned_to_nat(135);
    v___x_3006_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__1;
    v___x_3007_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3008_ = l_mkPanicMessageWithDecl(
        v___x_3007_,
        v___x_3006_,
        v___x_3005_,
        v___x_3004_,
        v___x_3003_,
    );
    return v___x_3008_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(
    mut v_simpFn_3009_: *mut LeanObject,
    mut v_e_3010_: *mut LeanObject,
    mut v_i_3011_: *mut LeanObject,
    mut v_a_3012_: *mut LeanObject,
    mut v_a_3013_: *mut LeanObject,
    mut v_a_3014_: *mut LeanObject,
    mut v_a_3015_: *mut LeanObject,
    mut v_a_3016_: *mut LeanObject,
    mut v_a_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
    mut v_a_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: u8 = 0;
    let mut v_fn_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3036_: u8 = 0;
    let mut v_binderType_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v___x_3056_: u8 = 0;
    let mut v_contextDependent_3057_: u8 = 0;
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3064_: u8 = 0;
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut v_a_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_a_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3080_: u8 = 0;
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3084_: u8 = 0;
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3022_ = lean_unsigned_to_nat(0);
                v___x_3023_ = lean_nat_dec_eq(v_i_3011_, v___x_3022_);
                if v___x_3023_ == 0 {
                    if lean_obj_tag(v_e_3010_) == 5 {
                        v_fn_3024_ = lean_ctor_get(v_e_3010_, 0);
                        lean_inc_ref_n(v_fn_3024_, 2);
                        v_arg_3025_ = lean_ctor_get(v_e_3010_, 1);
                        lean_inc_ref(v_arg_3025_);
                        v___x_3026_ = lean_unsigned_to_nat(1);
                        v_i_3027_ = lean_nat_sub(v_i_3011_, v___x_3026_);
                        v___x_3028_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(v_simpFn_3009_, v_fn_3024_, v_i_3027_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
                        lean_dec(v_i_3027_);
                        if lean_obj_tag(v___x_3028_) == 0 {
                            v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
                            lean_inc(v_a_3029_);
                            lean_dec_ref_known(v___x_3028_, 1);
                            lean_inc_ref(v_fn_3024_);
                            v___x_3030_ = l_Lean_Meta_Sym_inferType___redArg(
                                v_fn_3024_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                            );
                            if lean_obj_tag(v___x_3030_) == 0 {
                                v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
                                lean_inc(v_a_3031_);
                                lean_dec_ref_known(v___x_3030_, 1);
                                v___x_3032_ = l_Lean_Meta_whnfD(
                                    v_a_3031_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                                );
                                if lean_obj_tag(v___x_3032_) == 0 {
                                    v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
                                    v_isSharedCheck_3068_ = (!lean_is_exclusive(v___x_3032_)) as u8;
                                    if v_isSharedCheck_3068_ == 0 {
                                        v___x_3035_ = v___x_3032_;
                                        v_isShared_3036_ = v_isSharedCheck_3068_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3033_);
                                        lean_dec(v___x_3032_);
                                        v___x_3035_ = lean_box(0);
                                        v_isShared_3036_ = v_isSharedCheck_3068_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3029_);
                                    lean_dec_ref(v_arg_3025_);
                                    lean_dec_ref(v_fn_3024_);
                                    lean_dec_ref_known(v_e_3010_, 2);
                                    v_a_3069_ = lean_ctor_get(v___x_3032_, 0);
                                    v_isSharedCheck_3076_ = (!lean_is_exclusive(v___x_3032_)) as u8;
                                    if v_isSharedCheck_3076_ == 0 {
                                        v___x_3071_ = v___x_3032_;
                                        v_isShared_3072_ = v_isSharedCheck_3076_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3069_);
                                        lean_dec(v___x_3032_);
                                        v___x_3071_ = lean_box(0);
                                        v_isShared_3072_ = v_isSharedCheck_3076_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_3029_);
                                lean_dec_ref(v_arg_3025_);
                                lean_dec_ref(v_fn_3024_);
                                lean_dec_ref_known(v_e_3010_, 2);
                                v_a_3077_ = lean_ctor_get(v___x_3030_, 0);
                                v_isSharedCheck_3084_ = (!lean_is_exclusive(v___x_3030_)) as u8;
                                if v_isSharedCheck_3084_ == 0 {
                                    v___x_3079_ = v___x_3030_;
                                    v_isShared_3080_ = v_isSharedCheck_3084_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_3077_);
                                    lean_dec(v___x_3030_);
                                    v___x_3079_ = lean_box(0);
                                    v_isShared_3080_ = v_isSharedCheck_3084_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_arg_3025_);
                            lean_dec_ref(v_fn_3024_);
                            lean_dec_ref_known(v_e_3010_, 2);
                            return v___x_3028_;
                        }
                    } else {
                        lean_dec_ref(v_e_3010_);
                        lean_dec_ref(v_simpFn_3009_);
                        v___x_3085_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__4);
                        v___x_3086_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_3085_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
                        return v___x_3086_;
                    }
                } else {
                    lean_inc(v_a_3020_);
                    lean_inc_ref(v_a_3019_);
                    lean_inc(v_a_3018_);
                    lean_inc_ref(v_a_3017_);
                    lean_inc(v_a_3016_);
                    lean_inc_ref(v_a_3015_);
                    lean_inc(v_a_3014_);
                    lean_inc_ref(v_a_3013_);
                    lean_inc(v_a_3012_);
                    v___x_3087_ = lean_apply_11(
                        v_simpFn_3009_,
                        v_e_3010_,
                        v_a_3012_,
                        v_a_3013_,
                        v_a_3014_,
                        v_a_3015_,
                        v_a_3016_,
                        v_a_3017_,
                        v_a_3018_,
                        v_a_3019_,
                        v_a_3020_,
                        lean_box(0),
                    );
                    return v___x_3087_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_3033_) == 7 {
                    v_binderType_3037_ = lean_ctor_get(v_a_3033_, 1);
                    lean_inc_ref(v_binderType_3037_);
                    v_body_3038_ = lean_ctor_get(v_a_3033_, 2);
                    lean_inc_ref(v_body_3038_);
                    lean_dec_ref_known(v_a_3033_, 3);
                    v___x_3056_ = l_Lean_Expr_hasLooseBVars(v_body_3038_);
                    lean_dec_ref(v_body_3038_);
                    if v___x_3056_ == 0 {
                        lean_del_object(v___x_3035_);
                        state = 2;
                        continue;
                    } else {
                        if v___x_3023_ == 0 {
                            lean_dec_ref(v_binderType_3037_);
                            if lean_obj_tag(v_a_3029_) == 0 {
                                lean_dec_ref(v_arg_3025_);
                                lean_dec_ref(v_fn_3024_);
                                lean_dec_ref_known(v_e_3010_, 2);
                                v_contextDependent_3057_ = lean_ctor_get_uint8(v_a_3029_, 1 as u32);
                                lean_dec_ref_known(v_a_3029_, 0);
                                v___x_3058_ =
                                    l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_3057_);
                                if v_isShared_3036_ == 0 {
                                    lean_ctor_set(v___x_3035_, 0, v___x_3058_);
                                    v___x_3060_ = v___x_3035_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
                                    v___x_3060_ = v_reuseFailAlloc_3061_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_3035_);
                                v_e_x27_3062_ = lean_ctor_get(v_a_3029_, 0);
                                lean_inc_ref(v_e_x27_3062_);
                                v_proof_3063_ = lean_ctor_get(v_a_3029_, 1);
                                lean_inc_ref(v_proof_3063_);
                                v_contextDependent_3064_ = lean_ctor_get_uint8(
                                    v_a_3029_,
                                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                                );
                                lean_dec_ref_known(v_a_3029_, 2);
                                v___x_3065_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_3010_, v_fn_3024_, v_arg_3025_, v_e_x27_3062_, v_proof_3063_, v___x_3023_, v_contextDependent_3064_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
                                return v___x_3065_;
                            }
                        } else {
                            lean_del_object(v___x_3035_);
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3035_);
                    lean_dec(v_a_3033_);
                    lean_dec(v_a_3029_);
                    lean_dec_ref(v_arg_3025_);
                    lean_dec_ref_known(v_e_3010_, 2);
                    lean_dec_ref(v_fn_3024_);
                    v___x_3066_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__3);
                    v___x_3067_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_3066_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
                    return v___x_3067_;
                }
            }
            2 => {
                v___x_3040_ = l_Lean_Meta_isProp(
                    v_binderType_3037_,
                    v_a_3017_,
                    v_a_3018_,
                    v_a_3019_,
                    v_a_3020_,
                );
                if lean_obj_tag(v___x_3040_) == 0 {
                    v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
                    lean_inc(v_a_3041_);
                    lean_dec_ref_known(v___x_3040_, 1);
                    v___x_3042_ = (lean_unbox(v_a_3041_) as u8);
                    lean_dec(v_a_3041_);
                    if v___x_3042_ == 0 {
                        lean_inc(v_a_3020_);
                        lean_inc_ref(v_a_3019_);
                        lean_inc(v_a_3018_);
                        lean_inc_ref(v_a_3017_);
                        lean_inc(v_a_3016_);
                        lean_inc_ref(v_a_3015_);
                        lean_inc(v_a_3014_);
                        lean_inc_ref(v_a_3013_);
                        lean_inc(v_a_3012_);
                        lean_inc_ref(v_arg_3025_);
                        v___x_3043_ = lean_sym_simp(
                            v_arg_3025_,
                            v_a_3012_,
                            v_a_3013_,
                            v_a_3014_,
                            v_a_3015_,
                            v_a_3016_,
                            v_a_3017_,
                            v_a_3018_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        if lean_obj_tag(v___x_3043_) == 0 {
                            v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
                            lean_inc(v_a_3044_);
                            lean_dec_ref_known(v___x_3043_, 1);
                            v___x_3045_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(
                                v_e_3010_,
                                v_fn_3024_,
                                v_arg_3025_,
                                v_a_3029_,
                                v_a_3044_,
                                v_a_3015_,
                                v_a_3016_,
                                v_a_3017_,
                                v_a_3018_,
                                v_a_3019_,
                                v_a_3020_,
                            );
                            return v___x_3045_;
                        } else {
                            lean_dec(v_a_3029_);
                            lean_dec_ref(v_arg_3025_);
                            lean_dec_ref(v_fn_3024_);
                            lean_dec_ref_known(v_e_3010_, 2);
                            return v___x_3043_;
                        }
                    } else {
                        v___x_3046_ = lean_alloc_ctor(0, 0, (2) as u32);
                        lean_ctor_set_uint8(v___x_3046_, 0 as u32, v___x_3023_);
                        lean_ctor_set_uint8(v___x_3046_, 1 as u32, v___x_3023_);
                        v___x_3047_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(
                            v_e_3010_,
                            v_fn_3024_,
                            v_arg_3025_,
                            v_a_3029_,
                            v___x_3046_,
                            v_a_3015_,
                            v_a_3016_,
                            v_a_3017_,
                            v_a_3018_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        return v___x_3047_;
                    }
                } else {
                    lean_dec(v_a_3029_);
                    lean_dec_ref(v_arg_3025_);
                    lean_dec_ref(v_fn_3024_);
                    lean_dec_ref_known(v_e_3010_, 2);
                    v_a_3048_ = lean_ctor_get(v___x_3040_, 0);
                    v_isSharedCheck_3055_ = (!lean_is_exclusive(v___x_3040_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v___x_3050_ = v___x_3040_;
                        v_isShared_3051_ = v_isSharedCheck_3055_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3048_);
                        lean_dec(v___x_3040_);
                        v___x_3050_ = lean_box(0);
                        v_isShared_3051_ = v_isSharedCheck_3055_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3051_ == 0 {
                    v___x_3053_ = v___x_3050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
                    v___x_3053_ = v_reuseFailAlloc_3054_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3053_;
            }
            5 => {
                return v___x_3060_;
            }
            6 => {
                if v_isShared_3072_ == 0 {
                    v___x_3074_ = v___x_3071_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
                    v___x_3074_ = v_reuseFailAlloc_3075_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3074_;
            }
            8 => {
                if v_isShared_3080_ == 0 {
                    v___x_3082_ = v___x_3079_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
                    v___x_3082_ = v_reuseFailAlloc_3083_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___boxed(
    mut v_simpFn_3088_: *mut LeanObject,
    mut v_e_3089_: *mut LeanObject,
    mut v_i_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
    mut v_a_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
    mut v_a_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3101_: *mut LeanObject = core::ptr::null_mut();
    v_res_3101_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(
        v_simpFn_3088_,
        v_e_3089_,
        v_i_3090_,
        v_a_3091_,
        v_a_3092_,
        v_a_3093_,
        v_a_3094_,
        v_a_3095_,
        v_a_3096_,
        v_a_3097_,
        v_a_3098_,
        v_a_3099_,
    );
    lean_dec(v_a_3099_);
    lean_dec_ref(v_a_3098_);
    lean_dec(v_a_3097_);
    lean_dec_ref(v_a_3096_);
    lean_dec(v_a_3095_);
    lean_dec_ref(v_a_3094_);
    lean_dec(v_a_3093_);
    lean_dec_ref(v_a_3092_);
    lean_dec(v_a_3091_);
    lean_dec(v_i_3090_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpOverApplied(
    mut v_e_3102_: *mut LeanObject,
    mut v_numArgs_3103_: *mut LeanObject,
    mut v_simpFn_3104_: *mut LeanObject,
    mut v_a_3105_: *mut LeanObject,
    mut v_a_3106_: *mut LeanObject,
    mut v_a_3107_: *mut LeanObject,
    mut v_a_3108_: *mut LeanObject,
    mut v_a_3109_: *mut LeanObject,
    mut v_a_3110_: *mut LeanObject,
    mut v_a_3111_: *mut LeanObject,
    mut v_a_3112_: *mut LeanObject,
    mut v_a_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    v___x_3115_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(
        v_simpFn_3104_,
        v_e_3102_,
        v_numArgs_3103_,
        v_a_3105_,
        v_a_3106_,
        v_a_3107_,
        v_a_3108_,
        v_a_3109_,
        v_a_3110_,
        v_a_3111_,
        v_a_3112_,
        v_a_3113_,
    );
    return v___x_3115_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpOverApplied___boxed(
    mut v_e_3116_: *mut LeanObject,
    mut v_numArgs_3117_: *mut LeanObject,
    mut v_simpFn_3118_: *mut LeanObject,
    mut v_a_3119_: *mut LeanObject,
    mut v_a_3120_: *mut LeanObject,
    mut v_a_3121_: *mut LeanObject,
    mut v_a_3122_: *mut LeanObject,
    mut v_a_3123_: *mut LeanObject,
    mut v_a_3124_: *mut LeanObject,
    mut v_a_3125_: *mut LeanObject,
    mut v_a_3126_: *mut LeanObject,
    mut v_a_3127_: *mut LeanObject,
    mut v_a_3128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3129_: *mut LeanObject = core::ptr::null_mut();
    v_res_3129_ = l_Lean_Meta_Sym_Simp_simpOverApplied(
        v_e_3116_,
        v_numArgs_3117_,
        v_simpFn_3118_,
        v_a_3119_,
        v_a_3120_,
        v_a_3121_,
        v_a_3122_,
        v_a_3123_,
        v_a_3124_,
        v_a_3125_,
        v_a_3126_,
        v_a_3127_,
    );
    lean_dec(v_a_3127_);
    lean_dec_ref(v_a_3126_);
    lean_dec(v_a_3125_);
    lean_dec_ref(v_a_3124_);
    lean_dec(v_a_3123_);
    lean_dec_ref(v_a_3122_);
    lean_dec(v_a_3121_);
    lean_dec_ref(v_a_3120_);
    lean_dec(v_a_3119_);
    lean_dec(v_numArgs_3117_);
    return v_res_3129_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1()
-> *mut LeanObject {
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    v___x_3131_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3132_ = lean_unsigned_to_nat(13);
    v___x_3133_ = lean_unsigned_to_nat(172);
    v___x_3134_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__0;
    v___x_3135_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3136_ = l_mkPanicMessageWithDecl(
        v___x_3135_,
        v___x_3134_,
        v___x_3133_,
        v___x_3132_,
        v___x_3131_,
    );
    return v___x_3136_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(
    mut v_simpFn_3137_: *mut LeanObject,
    mut v_e_3138_: *mut LeanObject,
    mut v_i_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
    mut v_a_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    v___x_3150_ = lean_unsigned_to_nat(0);
    v___x_3151_ = lean_nat_dec_eq(v_i_3139_, v___x_3150_);
    if v___x_3151_ == 0 {
        if lean_obj_tag(v_e_3138_) == 5 {
            let mut v_fn_3152_: *mut LeanObject = core::ptr::null_mut();
            let mut v_arg_3153_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_3155_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
            v_fn_3152_ = lean_ctor_get(v_e_3138_, 0);
            lean_inc_ref_n(v_fn_3152_, 2);
            v_arg_3153_ = lean_ctor_get(v_e_3138_, 1);
            lean_inc_ref(v_arg_3153_);
            v___x_3154_ = lean_unsigned_to_nat(1);
            v_i_3155_ = lean_nat_sub(v_i_3139_, v___x_3154_);
            v___x_3156_ =
                l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(
                    v_simpFn_3137_,
                    v_fn_3152_,
                    v_i_3155_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    v_a_3143_,
                    v_a_3144_,
                    v_a_3145_,
                    v_a_3146_,
                    v_a_3147_,
                    v_a_3148_,
                );
            lean_dec(v_i_3155_);
            if lean_obj_tag(v___x_3156_) == 0 {
                let mut v_a_3157_: *mut LeanObject = core::ptr::null_mut();
                v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
                lean_inc(v_a_3157_);
                if lean_obj_tag(v_a_3157_) == 0 {
                    lean_dec_ref_known(v_a_3157_, 0);
                    lean_dec_ref(v_arg_3153_);
                    lean_dec_ref_known(v_e_3138_, 2);
                    lean_dec_ref(v_fn_3152_);
                    return v___x_3156_;
                } else {
                    let mut v_e_x27_3158_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_proof_3159_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_done_3160_: u8 = 0;
                    let mut v_contextDependent_3161_: u8 = 0;
                    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_3156_, 1);
                    v_e_x27_3158_ = lean_ctor_get(v_a_3157_, 0);
                    lean_inc_ref(v_e_x27_3158_);
                    v_proof_3159_ = lean_ctor_get(v_a_3157_, 1);
                    lean_inc_ref(v_proof_3159_);
                    v_done_3160_ = lean_ctor_get_uint8(
                        v_a_3157_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_contextDependent_3161_ = lean_ctor_get_uint8(
                        v_a_3157_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    lean_dec_ref_known(v_a_3157_, 2);
                    v___x_3162_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_3138_, v_fn_3152_, v_arg_3153_, v_e_x27_3158_, v_proof_3159_, v_done_3160_, v_contextDependent_3161_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
                    return v___x_3162_;
                }
            } else {
                lean_dec_ref(v_arg_3153_);
                lean_dec_ref_known(v_e_3138_, 2);
                lean_dec_ref(v_fn_3152_);
                return v___x_3156_;
            }
        } else {
            let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_e_3138_);
            lean_dec_ref(v_simpFn_3137_);
            v___x_3163_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___closed__1);
            v___x_3164_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_3163_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
            return v___x_3164_;
        }
    } else {
        let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_a_3148_);
        lean_inc_ref(v_a_3147_);
        lean_inc(v_a_3146_);
        lean_inc_ref(v_a_3145_);
        lean_inc(v_a_3144_);
        lean_inc_ref(v_a_3143_);
        lean_inc(v_a_3142_);
        lean_inc_ref(v_a_3141_);
        lean_inc(v_a_3140_);
        v___x_3165_ = lean_apply_11(
            v_simpFn_3137_,
            v_e_3138_,
            v_a_3140_,
            v_a_3141_,
            v_a_3142_,
            v_a_3143_,
            v_a_3144_,
            v_a_3145_,
            v_a_3146_,
            v_a_3147_,
            v_a_3148_,
            lean_box(0),
        );
        return v___x_3165_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit___boxed(
    mut v_simpFn_3166_: *mut LeanObject,
    mut v_e_3167_: *mut LeanObject,
    mut v_i_3168_: *mut LeanObject,
    mut v_a_3169_: *mut LeanObject,
    mut v_a_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
    mut v_a_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_a_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3179_: *mut LeanObject = core::ptr::null_mut();
    v_res_3179_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(
            v_simpFn_3166_,
            v_e_3167_,
            v_i_3168_,
            v_a_3169_,
            v_a_3170_,
            v_a_3171_,
            v_a_3172_,
            v_a_3173_,
            v_a_3174_,
            v_a_3175_,
            v_a_3176_,
            v_a_3177_,
        );
    lean_dec(v_a_3177_);
    lean_dec_ref(v_a_3176_);
    lean_dec(v_a_3175_);
    lean_dec_ref(v_a_3174_);
    lean_dec(v_a_3173_);
    lean_dec_ref(v_a_3172_);
    lean_dec(v_a_3171_);
    lean_dec_ref(v_a_3170_);
    lean_dec(v_a_3169_);
    lean_dec(v_i_3168_);
    return v_res_3179_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_propagateOverApplied(
    mut v_e_3180_: *mut LeanObject,
    mut v_numArgs_3181_: *mut LeanObject,
    mut v_simpFn_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_a_3185_: *mut LeanObject,
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
    mut v_a_3188_: *mut LeanObject,
    mut v_a_3189_: *mut LeanObject,
    mut v_a_3190_: *mut LeanObject,
    mut v_a_3191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_propagateOverApplied_visit(
            v_simpFn_3182_,
            v_e_3180_,
            v_numArgs_3181_,
            v_a_3183_,
            v_a_3184_,
            v_a_3185_,
            v_a_3186_,
            v_a_3187_,
            v_a_3188_,
            v_a_3189_,
            v_a_3190_,
            v_a_3191_,
        );
    return v___x_3193_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_propagateOverApplied___boxed(
    mut v_e_3194_: *mut LeanObject,
    mut v_numArgs_3195_: *mut LeanObject,
    mut v_simpFn_3196_: *mut LeanObject,
    mut v_a_3197_: *mut LeanObject,
    mut v_a_3198_: *mut LeanObject,
    mut v_a_3199_: *mut LeanObject,
    mut v_a_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_a_3202_: *mut LeanObject,
    mut v_a_3203_: *mut LeanObject,
    mut v_a_3204_: *mut LeanObject,
    mut v_a_3205_: *mut LeanObject,
    mut v_a_3206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3207_: *mut LeanObject = core::ptr::null_mut();
    v_res_3207_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(
        v_e_3194_,
        v_numArgs_3195_,
        v_simpFn_3196_,
        v_a_3197_,
        v_a_3198_,
        v_a_3199_,
        v_a_3200_,
        v_a_3201_,
        v_a_3202_,
        v_a_3203_,
        v_a_3204_,
        v_a_3205_,
    );
    lean_dec(v_a_3205_);
    lean_dec_ref(v_a_3204_);
    lean_dec(v_a_3203_);
    lean_dec_ref(v_a_3202_);
    lean_dec(v_a_3201_);
    lean_dec_ref(v_a_3200_);
    lean_dec(v_a_3199_);
    lean_dec_ref(v_a_3198_);
    lean_dec(v_a_3197_);
    lean_dec(v_numArgs_3195_);
    return v_res_3207_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    v___x_3209_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__0;
    v___x_3210_ = l_Lean_stringToMessageData(v___x_3209_);
    return v___x_3210_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(
    mut v_type_3211_: *mut LeanObject,
    mut v_a_3212_: *mut LeanObject,
    mut v_a_3213_: *mut LeanObject,
    mut v_a_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
    mut v_a_3216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: u8 = 0;
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3218_ = l_Lean_Expr_isForall(v_type_3211_);
                if v___x_3218_ == 0 {
                    v___x_3219_ =
                        l_Lean_Meta_whnfD(v_type_3211_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
                    if lean_obj_tag(v___x_3219_) == 0 {
                        v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
                        lean_inc(v_a_3220_);
                        lean_dec_ref_known(v___x_3219_, 1);
                        v___x_3221_ = l_Lean_Expr_isForall(v_a_3220_);
                        if v___x_3221_ == 0 {
                            v___x_3222_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___closed__1);
                            v___x_3223_ = l_Lean_MessageData_ofExpr(v_a_3220_);
                            v___x_3224_ = l_Lean_indentD(v___x_3223_);
                            v___x_3225_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3225_, 0, v___x_3222_);
                            lean_ctor_set(v___x_3225_, 1, v___x_3224_);
                            v___x_3226_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(v___x_3225_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
                            v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
                            v_isSharedCheck_3234_ = (!lean_is_exclusive(v___x_3226_)) as u8;
                            if v_isSharedCheck_3234_ == 0 {
                                v___x_3229_ = v___x_3226_;
                                v_isShared_3230_ = v_isSharedCheck_3234_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3227_);
                                lean_dec(v___x_3226_);
                                v___x_3229_ = lean_box(0);
                                v_isShared_3230_ = v_isSharedCheck_3234_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_3235_ =
                                l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_3220_, v_a_3212_);
                            return v___x_3235_;
                        }
                    } else {
                        return v___x_3219_;
                    }
                } else {
                    v___x_3236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3236_, 0, v_type_3211_);
                    return v___x_3236_;
                }
            }
            1 => {
                if v_isShared_3230_ == 0 {
                    v___x_3232_ = v___x_3229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
                    v___x_3232_ = v_reuseFailAlloc_3233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg___boxed(
    mut v_type_3237_: *mut LeanObject,
    mut v_a_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
    mut v_a_3240_: *mut LeanObject,
    mut v_a_3241_: *mut LeanObject,
    mut v_a_3242_: *mut LeanObject,
    mut v_a_3243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3244_: *mut LeanObject = core::ptr::null_mut();
    v_res_3244_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(
        v_type_3237_,
        v_a_3238_,
        v_a_3239_,
        v_a_3240_,
        v_a_3241_,
        v_a_3242_,
    );
    lean_dec(v_a_3242_);
    lean_dec_ref(v_a_3241_);
    lean_dec(v_a_3240_);
    lean_dec_ref(v_a_3239_);
    lean_dec(v_a_3238_);
    return v_res_3244_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(
    mut v_type_3245_: *mut LeanObject,
    mut v_a_3246_: *mut LeanObject,
    mut v_a_3247_: *mut LeanObject,
    mut v_a_3248_: *mut LeanObject,
    mut v_a_3249_: *mut LeanObject,
    mut v_a_3250_: *mut LeanObject,
    mut v_a_3251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    v___x_3253_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(
        v_type_3245_,
        v_a_3247_,
        v_a_3248_,
        v_a_3249_,
        v_a_3250_,
        v_a_3251_,
    );
    return v___x_3253_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___boxed(
    mut v_type_3254_: *mut LeanObject,
    mut v_a_3255_: *mut LeanObject,
    mut v_a_3256_: *mut LeanObject,
    mut v_a_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3262_: *mut LeanObject = core::ptr::null_mut();
    v_res_3262_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall(
        v_type_3254_,
        v_a_3255_,
        v_a_3256_,
        v_a_3257_,
        v_a_3258_,
        v_a_3259_,
        v_a_3260_,
    );
    lean_dec(v_a_3260_);
    lean_dec_ref(v_a_3259_);
    lean_dec(v_a_3258_);
    lean_dec_ref(v_a_3257_);
    lean_dec(v_a_3256_);
    lean_dec_ref(v_a_3255_);
    return v_res_3262_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
    return v___x_3263_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(
    mut v_msg_3264_: *mut LeanObject,
    mut v___y_3265_: *mut LeanObject,
    mut v___y_3266_: *mut LeanObject,
    mut v___y_3267_: *mut LeanObject,
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986__overap_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    v___x_3272_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___closed__0);
    v___x_986__overap_3273_ = lean_panic_fn_borrowed(v___x_3272_, v_msg_3264_);
    lean_inc(v___y_3270_);
    lean_inc_ref(v___y_3269_);
    lean_inc(v___y_3268_);
    lean_inc_ref(v___y_3267_);
    lean_inc(v___y_3266_);
    lean_inc_ref(v___y_3265_);
    v___x_3274_ = lean_apply_7(
        v___x_986__overap_3273_,
        v___y_3265_,
        v___y_3266_,
        v___y_3267_,
        v___y_3268_,
        v___y_3269_,
        v___y_3270_,
        lean_box(0),
    );
    return v___x_3274_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0___boxed(
    mut v_msg_3275_: *mut LeanObject,
    mut v___y_3276_: *mut LeanObject,
    mut v___y_3277_: *mut LeanObject,
    mut v___y_3278_: *mut LeanObject,
    mut v___y_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3283_: *mut LeanObject = core::ptr::null_mut();
    v_res_3283_ =
        l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(
            v_msg_3275_,
            v___y_3276_,
            v___y_3277_,
            v___y_3278_,
            v___y_3279_,
            v___y_3280_,
            v___y_3281_,
        );
    lean_dec(v___y_3281_);
    lean_dec_ref(v___y_3280_);
    lean_dec(v___y_3279_);
    lean_dec_ref(v___y_3278_);
    lean_dec(v___y_3277_);
    lean_dec_ref(v___y_3276_);
    return v_res_3283_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1()
-> *mut LeanObject {
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    v___x_3285_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3286_ = lean_unsigned_to_nat(47);
    v___x_3287_ = lean_unsigned_to_nat(203);
    v___x_3288_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__0;
    v___x_3289_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3290_ = l_mkPanicMessageWithDecl(
        v___x_3289_,
        v___x_3288_,
        v___x_3287_,
        v___x_3286_,
        v___x_3285_,
    );
    return v___x_3290_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(
    mut v_e_3291_: *mut LeanObject,
    mut v_n_3292_: *mut LeanObject,
    mut v_a_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
    mut v_a_3295_: *mut LeanObject,
    mut v_a_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3301_: u8 = 0;
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v_body_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3300_ = lean_unsigned_to_nat(0);
                v_isZero_3301_ = lean_nat_dec_eq(v_n_3292_, v_zero_3300_);
                if v_isZero_3301_ == 1 {
                    v___x_3302_ = l_Lean_Meta_Sym_inferType___redArg(
                        v_e_3291_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_,
                    );
                    return v___x_3302_;
                } else {
                    v_one_3303_ = lean_unsigned_to_nat(1);
                    v_n_3304_ = lean_nat_sub(v_n_3292_, v_one_3303_);
                    v___x_3305_ = l_Lean_Expr_appFn_x21(v_e_3291_);
                    lean_dec_ref(v_e_3291_);
                    v___x_3306_ =
                        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(
                            v___x_3305_,
                            v_n_3304_,
                            v_a_3293_,
                            v_a_3294_,
                            v_a_3295_,
                            v_a_3296_,
                            v_a_3297_,
                            v_a_3298_,
                        );
                    lean_dec(v_n_3304_);
                    if lean_obj_tag(v___x_3306_) == 0 {
                        v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
                        lean_inc(v_a_3307_);
                        lean_dec_ref_known(v___x_3306_, 1);
                        v___x_3308_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_a_3307_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
                        if lean_obj_tag(v___x_3308_) == 0 {
                            v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
                            v_isSharedCheck_3319_ = (!lean_is_exclusive(v___x_3308_)) as u8;
                            if v_isSharedCheck_3319_ == 0 {
                                v___x_3311_ = v___x_3308_;
                                v_isShared_3312_ = v_isSharedCheck_3319_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3309_);
                                lean_dec(v___x_3308_);
                                v___x_3311_ = lean_box(0);
                                v_isShared_3312_ = v_isSharedCheck_3319_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3308_;
                        }
                    } else {
                        return v___x_3306_;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3309_) == 7 {
                    v_body_3313_ = lean_ctor_get(v_a_3309_, 2);
                    lean_inc_ref(v_body_3313_);
                    lean_dec_ref_known(v_a_3309_, 3);
                    if v_isShared_3312_ == 0 {
                        lean_ctor_set(v___x_3311_, 0, v_body_3313_);
                        v___x_3315_ = v___x_3311_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_body_3313_);
                        v___x_3315_ = v_reuseFailAlloc_3316_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3311_);
                    lean_dec(v_a_3309_);
                    v___x_3317_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___closed__1);
                    v___x_3318_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType_spec__0(v___x_3317_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
                    return v___x_3318_;
                }
            }
            2 => {
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType___boxed(
    mut v_e_3320_: *mut LeanObject,
    mut v_n_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v_a_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
    mut v_a_3327_: *mut LeanObject,
    mut v_a_3328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3329_: *mut LeanObject = core::ptr::null_mut();
    v_res_3329_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(
        v_e_3320_, v_n_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_,
    );
    lean_dec(v_a_3327_);
    lean_dec_ref(v_a_3326_);
    lean_dec(v_a_3325_);
    lean_dec_ref(v_a_3324_);
    lean_dec(v_a_3323_);
    lean_dec_ref(v_a_3322_);
    lean_dec(v_n_3321_);
    return v_res_3329_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(
    mut v_f_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3344_: u8 = 0;
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3343_ = lean_st_ref_get(v___y_3333_);
                v_debug_3344_ = lean_ctor_get_uint8(
                    v___x_3343_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_3343_);
                if v_debug_3344_ == 0 {
                    v___y_3340_ = v___y_3333_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_f_3330_);
                    v___x_3345_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_3330_,
                        v___y_3332_,
                        v___y_3333_,
                        v___y_3334_,
                        v___y_3335_,
                        v___y_3336_,
                        v___y_3337_,
                    );
                    if lean_obj_tag(v___x_3345_) == 0 {
                        lean_dec_ref_known(v___x_3345_, 1);
                        lean_inc_ref(v_a_3331_);
                        v___x_3346_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_3331_,
                            v___y_3332_,
                            v___y_3333_,
                            v___y_3334_,
                            v___y_3335_,
                            v___y_3336_,
                            v___y_3337_,
                        );
                        if lean_obj_tag(v___x_3346_) == 0 {
                            lean_dec_ref_known(v___x_3346_, 1);
                            v___y_3340_ = v___y_3333_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_a_3331_);
                            lean_dec_ref(v_f_3330_);
                            v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
                            v_isSharedCheck_3354_ = (!lean_is_exclusive(v___x_3346_)) as u8;
                            if v_isSharedCheck_3354_ == 0 {
                                v___x_3349_ = v___x_3346_;
                                v_isShared_3350_ = v_isSharedCheck_3354_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3347_);
                                lean_dec(v___x_3346_);
                                v___x_3349_ = lean_box(0);
                                v_isShared_3350_ = v_isSharedCheck_3354_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_a_3331_);
                        lean_dec_ref(v_f_3330_);
                        v_a_3355_ = lean_ctor_get(v___x_3345_, 0);
                        v_isSharedCheck_3362_ = (!lean_is_exclusive(v___x_3345_)) as u8;
                        if v_isSharedCheck_3362_ == 0 {
                            v___x_3357_ = v___x_3345_;
                            v_isShared_3358_ = v_isSharedCheck_3362_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3355_);
                            lean_dec(v___x_3345_);
                            v___x_3357_ = lean_box(0);
                            v_isShared_3358_ = v_isSharedCheck_3362_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3341_ = l_Lean_Expr_app___override(v_f_3330_, v_a_3331_);
                v___x_3342_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3341_, v___y_3340_);
                return v___x_3342_;
            }
            2 => {
                if v_isShared_3350_ == 0 {
                    v___x_3352_ = v___x_3349_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
                    v___x_3352_ = v_reuseFailAlloc_3353_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3352_;
            }
            4 => {
                if v_isShared_3358_ == 0 {
                    v___x_3360_ = v___x_3357_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
                    v___x_3360_ = v_reuseFailAlloc_3361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg___boxed(
    mut v_f_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3372_: *mut LeanObject = core::ptr::null_mut();
    v_res_3372_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_3363_, v_a_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
    lean_dec(v___y_3370_);
    lean_dec_ref(v___y_3369_);
    lean_dec(v___y_3368_);
    lean_dec_ref(v___y_3367_);
    lean_dec(v___y_3366_);
    lean_dec_ref(v___y_3365_);
    return v_res_3372_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(
    mut v_f_3373_: *mut LeanObject,
    mut v_a_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    v___x_3385_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_f_3373_, v_a_3374_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
    return v___x_3385_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___boxed(
    mut v_f_3386_: *mut LeanObject,
    mut v_a_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3398_: *mut LeanObject = core::ptr::null_mut();
    v_res_3398_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0(v_f_3386_, v_a_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
    lean_dec(v___y_3396_);
    lean_dec_ref(v___y_3395_);
    lean_dec(v___y_3394_);
    lean_dec_ref(v___y_3393_);
    lean_dec(v___y_3392_);
    lean_dec_ref(v___y_3391_);
    lean_dec(v___y_3390_);
    lean_dec_ref(v___y_3389_);
    lean_dec(v___y_3388_);
    return v_res_3398_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
    return v___x_3399_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(
    mut v_msg_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_31792__overap_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    v___x_3411_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___closed__0);
    v___x_31792__overap_3412_ = lean_panic_fn_borrowed(v___x_3411_, v_msg_3400_);
    lean_inc(v___y_3409_);
    lean_inc_ref(v___y_3408_);
    lean_inc(v___y_3407_);
    lean_inc_ref(v___y_3406_);
    lean_inc(v___y_3405_);
    lean_inc_ref(v___y_3404_);
    lean_inc(v___y_3403_);
    lean_inc_ref(v___y_3402_);
    lean_inc(v___y_3401_);
    v___x_3413_ = lean_apply_10(
        v___x_31792__overap_3412_,
        v___y_3401_,
        v___y_3402_,
        v___y_3403_,
        v___y_3404_,
        v___y_3405_,
        v___y_3406_,
        v___y_3407_,
        v___y_3408_,
        v___y_3409_,
        lean_box(0),
    );
    return v___x_3413_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1___boxed(
    mut v_msg_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
    mut v___y_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
    mut v___y_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3425_: *mut LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v_msg_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
    lean_dec(v___y_3423_);
    lean_dec_ref(v___y_3422_);
    lean_dec(v___y_3421_);
    lean_dec_ref(v___y_3420_);
    lean_dec(v___y_3419_);
    lean_dec_ref(v___y_3418_);
    lean_dec(v___y_3417_);
    lean_dec_ref(v___y_3416_);
    lean_dec(v___y_3415_);
    return v_res_3425_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2()
-> *mut LeanObject {
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    v___x_3429_ = lean_box(0);
    v___x_3430_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__1;
    v___x_3431_ = l_Lean_Expr_const___override(v___x_3430_, v___x_3429_);
    return v___x_3431_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4()
-> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3434_ = lean_unsigned_to_nat(52);
    v___x_3435_ = lean_unsigned_to_nat(265);
    v___x_3436_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
    v___x_3437_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3438_ = l_mkPanicMessageWithDecl(
        v___x_3437_,
        v___x_3436_,
        v___x_3435_,
        v___x_3434_,
        v___x_3433_,
    );
    return v___x_3438_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5()
-> *mut LeanObject {
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    v___x_3439_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3440_ = lean_unsigned_to_nat(52);
    v___x_3441_ = lean_unsigned_to_nat(257);
    v___x_3442_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
    v___x_3443_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3444_ = l_mkPanicMessageWithDecl(
        v___x_3443_,
        v___x_3442_,
        v___x_3441_,
        v___x_3440_,
        v___x_3439_,
    );
    return v___x_3444_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6()
-> *mut LeanObject {
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    v___x_3445_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3446_ = lean_unsigned_to_nat(52);
    v___x_3447_ = lean_unsigned_to_nat(272);
    v___x_3448_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
    v___x_3449_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3450_ = l_mkPanicMessageWithDecl(
        v___x_3449_,
        v___x_3448_,
        v___x_3447_,
        v___x_3446_,
        v___x_3445_,
    );
    return v___x_3450_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7()
-> *mut LeanObject {
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    v___x_3451_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3452_ = lean_unsigned_to_nat(26);
    v___x_3453_ = lean_unsigned_to_nat(250);
    v___x_3454_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__3;
    v___x_3455_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3456_ = l_mkPanicMessageWithDecl(
        v___x_3455_,
        v___x_3454_,
        v___x_3453_,
        v___x_3452_,
        v___x_3451_,
    );
    return v___x_3456_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9()
-> *mut LeanObject {
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    v___x_3459_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
    v___x_3460_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
    v___x_3461_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3461_, 0, v___x_3460_);
    lean_ctor_set(v___x_3461_, 1, v___x_3459_);
    return v___x_3461_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(
    mut v_i_3462_: *mut LeanObject,
    mut v_e_3463_: *mut LeanObject,
    mut v_a_3464_: *mut LeanObject,
    mut v_a_3465_: *mut LeanObject,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
    mut v_a_3468_: *mut LeanObject,
    mut v_a_3469_: *mut LeanObject,
    mut v_a_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
    mut v_a_3472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v_fn_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3491_: u8 = 0;
    let mut v___y_3493_: u8 = 0;
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: u8 = 0;
    let mut v_contextDependent_3503_: u8 = 0;
    let mut v_contextDependent_3504_: u8 = 0;
    let mut v_contextDependent_3505_: u8 = 0;
    let mut v_e_x27_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3508_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3534_: u8 = 0;
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_a_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut v_a_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_a_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3562_: u8 = 0;
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3566_: u8 = 0;
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3576_: u8 = 0;
    let mut v_a_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_isSharedCheck_3585_: u8 = 0;
    let mut v_e_x27_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3588_: u8 = 0;
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v_contextDependent_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3605_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: u8 = 0;
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3621_: u8 = 0;
    let mut v_a_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3625_: u8 = 0;
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3629_: u8 = 0;
    let mut v_a_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut v_a_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut v_isSharedCheck_3656_: u8 = 0;
    let mut v_e_x27_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3659_: u8 = 0;
    let mut v_e_x27_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3662_: u8 = 0;
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3678_: u8 = 0;
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: u8 = 0;
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_a_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut v_a_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut v_a_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v_isSharedCheck_3730_: u8 = 0;
    let mut v_a_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3734_: u8 = 0;
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3738_: u8 = 0;
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3474_ = lean_unsigned_to_nat(0);
                v___x_3475_ = lean_nat_dec_eq(v_i_3462_, v___x_3474_);
                if v___x_3475_ == 0 {
                    if lean_obj_tag(v_e_3463_) == 5 {
                        v_fn_3476_ = lean_ctor_get(v_e_3463_, 0);
                        lean_inc_ref_n(v_fn_3476_, 2);
                        v_arg_3477_ = lean_ctor_get(v_e_3463_, 1);
                        lean_inc_ref(v_arg_3477_);
                        lean_dec_ref_known(v_e_3463_, 2);
                        v___x_3478_ = lean_unsigned_to_nat(1);
                        v___x_3479_ = lean_nat_sub(v_i_3462_, v___x_3478_);
                        v___x_3480_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(v___x_3479_, v_fn_3476_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                        if lean_obj_tag(v___x_3480_) == 0 {
                            v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
                            lean_inc(v_a_3481_);
                            lean_dec_ref_known(v___x_3480_, 1);
                            v_fst_3482_ = lean_ctor_get(v_a_3481_, 0);
                            v_snd_3483_ = lean_ctor_get(v_a_3481_, 1);
                            v_isSharedCheck_3739_ = (!lean_is_exclusive(v_a_3481_)) as u8;
                            if v_isSharedCheck_3739_ == 0 {
                                v___x_3485_ = v_a_3481_;
                                v_isShared_3486_ = v_isSharedCheck_3739_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_3483_);
                                lean_inc(v_fst_3482_);
                                lean_dec(v_a_3481_);
                                v___x_3485_ = lean_box(0);
                                v_isShared_3486_ = v_isSharedCheck_3739_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3479_);
                            lean_dec_ref(v_arg_3477_);
                            lean_dec_ref(v_fn_3476_);
                            return v___x_3480_;
                        }
                    } else {
                        lean_dec_ref(v_e_3463_);
                        v___x_3740_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__7);
                        v___x_3741_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_3740_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                        return v___x_3741_;
                    }
                } else {
                    lean_dec_ref(v_e_3463_);
                    v___x_3742_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__9);
                    v___x_3743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3743_, 0, v___x_3742_);
                    return v___x_3743_;
                }
            }
            1 => {
                lean_inc(v_a_3472_);
                lean_inc_ref(v_a_3471_);
                lean_inc(v_a_3470_);
                lean_inc_ref(v_a_3469_);
                lean_inc(v_a_3468_);
                lean_inc_ref(v_a_3467_);
                lean_inc(v_a_3466_);
                lean_inc_ref(v_a_3465_);
                lean_inc(v_a_3464_);
                lean_inc_ref(v_arg_3477_);
                v___x_3487_ = lean_sym_simp(
                    v_arg_3477_,
                    v_a_3464_,
                    v_a_3465_,
                    v_a_3466_,
                    v_a_3467_,
                    v_a_3468_,
                    v_a_3469_,
                    v_a_3470_,
                    v_a_3471_,
                    v_a_3472_,
                );
                if lean_obj_tag(v___x_3487_) == 0 {
                    v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
                    v_isSharedCheck_3730_ = (!lean_is_exclusive(v___x_3487_)) as u8;
                    if v_isSharedCheck_3730_ == 0 {
                        v___x_3490_ = v___x_3487_;
                        v_isShared_3491_ = v_isSharedCheck_3730_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3488_);
                        lean_dec(v___x_3487_);
                        v___x_3490_ = lean_box(0);
                        v_isShared_3491_ = v_isSharedCheck_3730_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3485_);
                    lean_dec(v_snd_3483_);
                    lean_dec(v_fst_3482_);
                    lean_dec(v___x_3479_);
                    lean_dec_ref(v_arg_3477_);
                    lean_dec_ref(v_fn_3476_);
                    v_a_3731_ = lean_ctor_get(v___x_3487_, 0);
                    v_isSharedCheck_3738_ = (!lean_is_exclusive(v___x_3487_)) as u8;
                    if v_isSharedCheck_3738_ == 0 {
                        v___x_3733_ = v___x_3487_;
                        v_isShared_3734_ = v_isSharedCheck_3738_;
                        state = 47;
                        continue;
                    } else {
                        lean_inc(v_a_3731_);
                        lean_dec(v___x_3487_);
                        v___x_3733_ = lean_box(0);
                        v_isShared_3734_ = v_isSharedCheck_3738_;
                        state = 47;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3502_ = 1;
                if lean_obj_tag(v_fst_3482_) == 0 {
                    lean_dec(v_snd_3483_);
                    if lean_obj_tag(v_a_3488_) == 0 {
                        lean_dec(v___x_3479_);
                        lean_dec_ref(v_arg_3477_);
                        lean_dec_ref(v_fn_3476_);
                        v_contextDependent_3503_ = lean_ctor_get_uint8(v_fst_3482_, 1 as u32);
                        lean_dec_ref_known(v_fst_3482_, 0);
                        if v_contextDependent_3503_ == 0 {
                            v_contextDependent_3504_ = lean_ctor_get_uint8(v_a_3488_, 1 as u32);
                            lean_dec_ref_known(v_a_3488_, 0);
                            v___y_3493_ = v_contextDependent_3504_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref_known(v_a_3488_, 0);
                            v___y_3493_ = v___x_3502_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3490_);
                        lean_del_object(v___x_3485_);
                        v_contextDependent_3505_ = lean_ctor_get_uint8(v_fst_3482_, 1 as u32);
                        lean_dec_ref_known(v_fst_3482_, 0);
                        v_e_x27_3506_ = lean_ctor_get(v_a_3488_, 0);
                        v_proof_3507_ = lean_ctor_get(v_a_3488_, 1);
                        v_contextDependent_3508_ = lean_ctor_get_uint8(
                            v_a_3488_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v_isSharedCheck_3585_ = (!lean_is_exclusive(v_a_3488_)) as u8;
                        if v_isSharedCheck_3585_ == 0 {
                            v___x_3510_ = v_a_3488_;
                            v_isShared_3511_ = v_isSharedCheck_3585_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_proof_3507_);
                            lean_inc(v_e_x27_3506_);
                            lean_dec(v_a_3488_);
                            v___x_3510_ = lean_box(0);
                            v_isShared_3511_ = v_isSharedCheck_3585_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3490_);
                    lean_del_object(v___x_3485_);
                    lean_dec(v___x_3479_);
                    if lean_obj_tag(v_a_3488_) == 0 {
                        v_e_x27_3586_ = lean_ctor_get(v_fst_3482_, 0);
                        v_proof_3587_ = lean_ctor_get(v_fst_3482_, 1);
                        v_contextDependent_3588_ = lean_ctor_get_uint8(
                            v_fst_3482_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v_isSharedCheck_3656_ = (!lean_is_exclusive(v_fst_3482_)) as u8;
                        if v_isSharedCheck_3656_ == 0 {
                            v___x_3590_ = v_fst_3482_;
                            v_isShared_3591_ = v_isSharedCheck_3656_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_proof_3587_);
                            lean_inc(v_e_x27_3586_);
                            lean_dec(v_fst_3482_);
                            v___x_3590_ = lean_box(0);
                            v_isShared_3591_ = v_isSharedCheck_3656_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_e_x27_3657_ = lean_ctor_get(v_fst_3482_, 0);
                        lean_inc_ref(v_e_x27_3657_);
                        v_proof_3658_ = lean_ctor_get(v_fst_3482_, 1);
                        lean_inc_ref(v_proof_3658_);
                        v_contextDependent_3659_ = lean_ctor_get_uint8(
                            v_fst_3482_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        lean_dec_ref_known(v_fst_3482_, 2);
                        v_e_x27_3660_ = lean_ctor_get(v_a_3488_, 0);
                        v_proof_3661_ = lean_ctor_get(v_a_3488_, 1);
                        v_contextDependent_3662_ = lean_ctor_get_uint8(
                            v_a_3488_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v_isSharedCheck_3729_ = (!lean_is_exclusive(v_a_3488_)) as u8;
                        if v_isSharedCheck_3729_ == 0 {
                            v___x_3664_ = v_a_3488_;
                            v_isShared_3665_ = v_isSharedCheck_3729_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_proof_3661_);
                            lean_inc(v_e_x27_3660_);
                            lean_dec(v_a_3488_);
                            v___x_3664_ = lean_box(0);
                            v_isShared_3665_ = v_isSharedCheck_3729_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_3494_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_3493_);
                v___x_3495_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__2);
                if v_isShared_3486_ == 0 {
                    lean_ctor_set(v___x_3485_, 1, v___x_3495_);
                    lean_ctor_set(v___x_3485_, 0, v___x_3494_);
                    v___x_3497_ = v___x_3485_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3494_);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3495_);
                    v___x_3497_ = v_reuseFailAlloc_3501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3491_ == 0 {
                    lean_ctor_set(v___x_3490_, 0, v___x_3497_);
                    v___x_3499_ = v___x_3490_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
                    v___x_3499_ = v_reuseFailAlloc_3500_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3499_;
            }
            6 => {
                lean_inc_ref(v_fn_3476_);
                v___x_3512_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_getFnType(
                    v_fn_3476_,
                    v___x_3479_,
                    v_a_3467_,
                    v_a_3468_,
                    v_a_3469_,
                    v_a_3470_,
                    v_a_3471_,
                    v_a_3472_,
                );
                lean_dec(v___x_3479_);
                if lean_obj_tag(v___x_3512_) == 0 {
                    v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
                    lean_inc(v_a_3513_);
                    lean_dec_ref_known(v___x_3512_, 1);
                    v___x_3514_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(v_a_3513_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                    if lean_obj_tag(v___x_3514_) == 0 {
                        v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
                        lean_inc(v_a_3515_);
                        lean_dec_ref_known(v___x_3514_, 1);
                        if lean_obj_tag(v_a_3515_) == 7 {
                            v_binderType_3516_ = lean_ctor_get(v_a_3515_, 1);
                            lean_inc_ref(v_binderType_3516_);
                            v_body_3517_ = lean_ctor_get(v_a_3515_, 2);
                            lean_inc_ref(v_body_3517_);
                            lean_dec_ref_known(v_a_3515_, 3);
                            lean_inc_ref(v_e_x27_3506_);
                            lean_inc_ref(v_fn_3476_);
                            v___x_3518_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_fn_3476_, v_e_x27_3506_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                            if lean_obj_tag(v___x_3518_) == 0 {
                                v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
                                lean_inc(v_a_3519_);
                                lean_dec_ref_known(v___x_3518_, 1);
                                lean_inc_ref(v_binderType_3516_);
                                v___x_3520_ = l_Lean_Meta_Sym_getLevel___redArg(
                                    v_binderType_3516_,
                                    v_a_3468_,
                                    v_a_3469_,
                                    v_a_3470_,
                                    v_a_3471_,
                                    v_a_3472_,
                                );
                                if lean_obj_tag(v___x_3520_) == 0 {
                                    v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
                                    lean_inc(v_a_3521_);
                                    lean_dec_ref_known(v___x_3520_, 1);
                                    lean_inc_ref(v_body_3517_);
                                    v___x_3522_ = l_Lean_Meta_Sym_getLevel___redArg(
                                        v_body_3517_,
                                        v_a_3468_,
                                        v_a_3469_,
                                        v_a_3470_,
                                        v_a_3471_,
                                        v_a_3472_,
                                    );
                                    if lean_obj_tag(v___x_3522_) == 0 {
                                        v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
                                        v_isSharedCheck_3542_ =
                                            (!lean_is_exclusive(v___x_3522_)) as u8;
                                        if v_isSharedCheck_3542_ == 0 {
                                            v___x_3525_ = v___x_3522_;
                                            v_isShared_3526_ = v_isSharedCheck_3542_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3523_);
                                            lean_dec(v___x_3522_);
                                            v___x_3525_ = lean_box(0);
                                            v_isShared_3526_ = v_isSharedCheck_3542_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_3521_);
                                        lean_dec(v_a_3519_);
                                        lean_dec_ref(v_body_3517_);
                                        lean_dec_ref(v_binderType_3516_);
                                        lean_del_object(v___x_3510_);
                                        lean_dec_ref(v_proof_3507_);
                                        lean_dec_ref(v_e_x27_3506_);
                                        lean_dec_ref(v_arg_3477_);
                                        lean_dec_ref(v_fn_3476_);
                                        v_a_3543_ = lean_ctor_get(v___x_3522_, 0);
                                        v_isSharedCheck_3550_ =
                                            (!lean_is_exclusive(v___x_3522_)) as u8;
                                        if v_isSharedCheck_3550_ == 0 {
                                            v___x_3545_ = v___x_3522_;
                                            v_isShared_3546_ = v_isSharedCheck_3550_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3543_);
                                            lean_dec(v___x_3522_);
                                            v___x_3545_ = lean_box(0);
                                            v_isShared_3546_ = v_isSharedCheck_3550_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_3519_);
                                    lean_dec_ref(v_body_3517_);
                                    lean_dec_ref(v_binderType_3516_);
                                    lean_del_object(v___x_3510_);
                                    lean_dec_ref(v_proof_3507_);
                                    lean_dec_ref(v_e_x27_3506_);
                                    lean_dec_ref(v_arg_3477_);
                                    lean_dec_ref(v_fn_3476_);
                                    v_a_3551_ = lean_ctor_get(v___x_3520_, 0);
                                    v_isSharedCheck_3558_ = (!lean_is_exclusive(v___x_3520_)) as u8;
                                    if v_isSharedCheck_3558_ == 0 {
                                        v___x_3553_ = v___x_3520_;
                                        v_isShared_3554_ = v_isSharedCheck_3558_;
                                        state = 13;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3551_);
                                        lean_dec(v___x_3520_);
                                        v___x_3553_ = lean_box(0);
                                        v_isShared_3554_ = v_isSharedCheck_3558_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_body_3517_);
                                lean_dec_ref(v_binderType_3516_);
                                lean_del_object(v___x_3510_);
                                lean_dec_ref(v_proof_3507_);
                                lean_dec_ref(v_e_x27_3506_);
                                lean_dec_ref(v_arg_3477_);
                                lean_dec_ref(v_fn_3476_);
                                v_a_3559_ = lean_ctor_get(v___x_3518_, 0);
                                v_isSharedCheck_3566_ = (!lean_is_exclusive(v___x_3518_)) as u8;
                                if v_isSharedCheck_3566_ == 0 {
                                    v___x_3561_ = v___x_3518_;
                                    v_isShared_3562_ = v_isSharedCheck_3566_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_3559_);
                                    lean_dec(v___x_3518_);
                                    v___x_3561_ = lean_box(0);
                                    v_isShared_3562_ = v_isSharedCheck_3566_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3515_);
                            lean_del_object(v___x_3510_);
                            lean_dec_ref(v_proof_3507_);
                            lean_dec_ref(v_e_x27_3506_);
                            lean_dec_ref(v_arg_3477_);
                            lean_dec_ref(v_fn_3476_);
                            v___x_3567_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__4);
                            v___x_3568_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_3567_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                            return v___x_3568_;
                        }
                    } else {
                        lean_del_object(v___x_3510_);
                        lean_dec_ref(v_proof_3507_);
                        lean_dec_ref(v_e_x27_3506_);
                        lean_dec_ref(v_arg_3477_);
                        lean_dec_ref(v_fn_3476_);
                        v_a_3569_ = lean_ctor_get(v___x_3514_, 0);
                        v_isSharedCheck_3576_ = (!lean_is_exclusive(v___x_3514_)) as u8;
                        if v_isSharedCheck_3576_ == 0 {
                            v___x_3571_ = v___x_3514_;
                            v_isShared_3572_ = v_isSharedCheck_3576_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3569_);
                            lean_dec(v___x_3514_);
                            v___x_3571_ = lean_box(0);
                            v_isShared_3572_ = v_isSharedCheck_3576_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3510_);
                    lean_dec_ref(v_proof_3507_);
                    lean_dec_ref(v_e_x27_3506_);
                    lean_dec_ref(v_arg_3477_);
                    lean_dec_ref(v_fn_3476_);
                    v_a_3577_ = lean_ctor_get(v___x_3512_, 0);
                    v_isSharedCheck_3584_ = (!lean_is_exclusive(v___x_3512_)) as u8;
                    if v_isSharedCheck_3584_ == 0 {
                        v___x_3579_ = v___x_3512_;
                        v_isShared_3580_ = v_isSharedCheck_3584_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3577_);
                        lean_dec(v___x_3512_);
                        v___x_3579_ = lean_box(0);
                        v_isShared_3580_ = v_isSharedCheck_3584_;
                        state = 19;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3527_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1;
                v___x_3528_ = lean_box(0);
                v___x_3529_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3529_, 0, v_a_3523_);
                lean_ctor_set(v___x_3529_, 1, v___x_3528_);
                v___x_3530_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3530_, 0, v_a_3521_);
                lean_ctor_set(v___x_3530_, 1, v___x_3529_);
                v___x_3531_ = l_Lean_mkConst(v___x_3527_, v___x_3530_);
                lean_inc_ref(v_body_3517_);
                v___x_3532_ = l_Lean_mkApp6(
                    v___x_3531_,
                    v_binderType_3516_,
                    v_body_3517_,
                    v_arg_3477_,
                    v_e_x27_3506_,
                    v_fn_3476_,
                    v_proof_3507_,
                );
                if v_contextDependent_3505_ == 0 {
                    v___y_3534_ = v_contextDependent_3508_;
                    state = 8;
                    continue;
                } else {
                    v___y_3534_ = v___x_3502_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3511_ == 0 {
                    lean_ctor_set(v___x_3510_, 1, v___x_3532_);
                    lean_ctor_set(v___x_3510_, 0, v_a_3519_);
                    v___x_3536_ = v___x_3510_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3519_);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 1, v___x_3532_);
                    v___x_3536_ = v_reuseFailAlloc_3541_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_ctor_set_uint8(
                    v___x_3536_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3475_,
                );
                lean_ctor_set_uint8(
                    v___x_3536_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_3534_,
                );
                v___x_3537_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3537_, 0, v___x_3536_);
                lean_ctor_set(v___x_3537_, 1, v_body_3517_);
                if v_isShared_3526_ == 0 {
                    lean_ctor_set(v___x_3525_, 0, v___x_3537_);
                    v___x_3539_ = v___x_3525_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
                    v___x_3539_ = v_reuseFailAlloc_3540_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3539_;
            }
            11 => {
                if v_isShared_3546_ == 0 {
                    v___x_3548_ = v___x_3545_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
                    v___x_3548_ = v_reuseFailAlloc_3549_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3548_;
            }
            13 => {
                if v_isShared_3554_ == 0 {
                    v___x_3556_ = v___x_3553_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
                    v___x_3556_ = v_reuseFailAlloc_3557_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3556_;
            }
            15 => {
                if v_isShared_3562_ == 0 {
                    v___x_3564_ = v___x_3561_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
                    v___x_3564_ = v_reuseFailAlloc_3565_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3564_;
            }
            17 => {
                if v_isShared_3572_ == 0 {
                    v___x_3574_ = v___x_3571_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
                    v___x_3574_ = v_reuseFailAlloc_3575_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3574_;
            }
            19 => {
                if v_isShared_3580_ == 0 {
                    v___x_3582_ = v___x_3579_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3582_;
            }
            21 => {
                v_contextDependent_3592_ = lean_ctor_get_uint8(v_a_3488_, 1 as u32);
                lean_dec_ref_known(v_a_3488_, 0);
                v___x_3593_ =
                    l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(
                        v_snd_3483_,
                        v_a_3468_,
                        v_a_3469_,
                        v_a_3470_,
                        v_a_3471_,
                        v_a_3472_,
                    );
                if lean_obj_tag(v___x_3593_) == 0 {
                    v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
                    lean_inc(v_a_3594_);
                    lean_dec_ref_known(v___x_3593_, 1);
                    if lean_obj_tag(v_a_3594_) == 7 {
                        v_binderType_3595_ = lean_ctor_get(v_a_3594_, 1);
                        lean_inc_ref(v_binderType_3595_);
                        v_body_3596_ = lean_ctor_get(v_a_3594_, 2);
                        lean_inc_ref(v_body_3596_);
                        lean_dec_ref_known(v_a_3594_, 3);
                        lean_inc_ref(v_arg_3477_);
                        lean_inc_ref(v_e_x27_3586_);
                        v___x_3597_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_3586_, v_arg_3477_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                        if lean_obj_tag(v___x_3597_) == 0 {
                            v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
                            lean_inc(v_a_3598_);
                            lean_dec_ref_known(v___x_3597_, 1);
                            lean_inc_ref(v_binderType_3595_);
                            v___x_3599_ = l_Lean_Meta_Sym_getLevel___redArg(
                                v_binderType_3595_,
                                v_a_3468_,
                                v_a_3469_,
                                v_a_3470_,
                                v_a_3471_,
                                v_a_3472_,
                            );
                            if lean_obj_tag(v___x_3599_) == 0 {
                                v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
                                lean_inc(v_a_3600_);
                                lean_dec_ref_known(v___x_3599_, 1);
                                lean_inc_ref(v_body_3596_);
                                v___x_3601_ = l_Lean_Meta_Sym_getLevel___redArg(
                                    v_body_3596_,
                                    v_a_3468_,
                                    v_a_3469_,
                                    v_a_3470_,
                                    v_a_3471_,
                                    v_a_3472_,
                                );
                                if lean_obj_tag(v___x_3601_) == 0 {
                                    v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
                                    v_isSharedCheck_3621_ = (!lean_is_exclusive(v___x_3601_)) as u8;
                                    if v_isSharedCheck_3621_ == 0 {
                                        v___x_3604_ = v___x_3601_;
                                        v_isShared_3605_ = v_isSharedCheck_3621_;
                                        state = 22;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3602_);
                                        lean_dec(v___x_3601_);
                                        v___x_3604_ = lean_box(0);
                                        v_isShared_3605_ = v_isSharedCheck_3621_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3600_);
                                    lean_dec(v_a_3598_);
                                    lean_dec_ref(v_body_3596_);
                                    lean_dec_ref(v_binderType_3595_);
                                    lean_del_object(v___x_3590_);
                                    lean_dec_ref(v_proof_3587_);
                                    lean_dec_ref(v_e_x27_3586_);
                                    lean_dec_ref(v_arg_3477_);
                                    lean_dec_ref(v_fn_3476_);
                                    v_a_3622_ = lean_ctor_get(v___x_3601_, 0);
                                    v_isSharedCheck_3629_ = (!lean_is_exclusive(v___x_3601_)) as u8;
                                    if v_isSharedCheck_3629_ == 0 {
                                        v___x_3624_ = v___x_3601_;
                                        v_isShared_3625_ = v_isSharedCheck_3629_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3622_);
                                        lean_dec(v___x_3601_);
                                        v___x_3624_ = lean_box(0);
                                        v_isShared_3625_ = v_isSharedCheck_3629_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_3598_);
                                lean_dec_ref(v_body_3596_);
                                lean_dec_ref(v_binderType_3595_);
                                lean_del_object(v___x_3590_);
                                lean_dec_ref(v_proof_3587_);
                                lean_dec_ref(v_e_x27_3586_);
                                lean_dec_ref(v_arg_3477_);
                                lean_dec_ref(v_fn_3476_);
                                v_a_3630_ = lean_ctor_get(v___x_3599_, 0);
                                v_isSharedCheck_3637_ = (!lean_is_exclusive(v___x_3599_)) as u8;
                                if v_isSharedCheck_3637_ == 0 {
                                    v___x_3632_ = v___x_3599_;
                                    v_isShared_3633_ = v_isSharedCheck_3637_;
                                    state = 28;
                                    continue;
                                } else {
                                    lean_inc(v_a_3630_);
                                    lean_dec(v___x_3599_);
                                    v___x_3632_ = lean_box(0);
                                    v_isShared_3633_ = v_isSharedCheck_3637_;
                                    state = 28;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_body_3596_);
                            lean_dec_ref(v_binderType_3595_);
                            lean_del_object(v___x_3590_);
                            lean_dec_ref(v_proof_3587_);
                            lean_dec_ref(v_e_x27_3586_);
                            lean_dec_ref(v_arg_3477_);
                            lean_dec_ref(v_fn_3476_);
                            v_a_3638_ = lean_ctor_get(v___x_3597_, 0);
                            v_isSharedCheck_3645_ = (!lean_is_exclusive(v___x_3597_)) as u8;
                            if v_isSharedCheck_3645_ == 0 {
                                v___x_3640_ = v___x_3597_;
                                v_isShared_3641_ = v_isSharedCheck_3645_;
                                state = 30;
                                continue;
                            } else {
                                lean_inc(v_a_3638_);
                                lean_dec(v___x_3597_);
                                v___x_3640_ = lean_box(0);
                                v_isShared_3641_ = v_isSharedCheck_3645_;
                                state = 30;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3594_);
                        lean_del_object(v___x_3590_);
                        lean_dec_ref(v_proof_3587_);
                        lean_dec_ref(v_e_x27_3586_);
                        lean_dec_ref(v_arg_3477_);
                        lean_dec_ref(v_fn_3476_);
                        v___x_3646_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__5);
                        v___x_3647_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_3646_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                        return v___x_3647_;
                    }
                } else {
                    lean_del_object(v___x_3590_);
                    lean_dec_ref(v_proof_3587_);
                    lean_dec_ref(v_e_x27_3586_);
                    lean_dec_ref(v_arg_3477_);
                    lean_dec_ref(v_fn_3476_);
                    v_a_3648_ = lean_ctor_get(v___x_3593_, 0);
                    v_isSharedCheck_3655_ = (!lean_is_exclusive(v___x_3593_)) as u8;
                    if v_isSharedCheck_3655_ == 0 {
                        v___x_3650_ = v___x_3593_;
                        v_isShared_3651_ = v_isSharedCheck_3655_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_a_3648_);
                        lean_dec(v___x_3593_);
                        v___x_3650_ = lean_box(0);
                        v_isShared_3651_ = v_isSharedCheck_3655_;
                        state = 32;
                        continue;
                    }
                }
            }
            22 => {
                v___x_3606_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3;
                v___x_3607_ = lean_box(0);
                v___x_3608_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3608_, 0, v_a_3602_);
                lean_ctor_set(v___x_3608_, 1, v___x_3607_);
                v___x_3609_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3609_, 0, v_a_3600_);
                lean_ctor_set(v___x_3609_, 1, v___x_3608_);
                v___x_3610_ = l_Lean_mkConst(v___x_3606_, v___x_3609_);
                lean_inc_ref(v_body_3596_);
                v___x_3611_ = l_Lean_mkApp6(
                    v___x_3610_,
                    v_binderType_3595_,
                    v_body_3596_,
                    v_fn_3476_,
                    v_e_x27_3586_,
                    v_proof_3587_,
                    v_arg_3477_,
                );
                if v_contextDependent_3588_ == 0 {
                    v___y_3613_ = v_contextDependent_3592_;
                    state = 23;
                    continue;
                } else {
                    v___y_3613_ = v___x_3502_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3591_ == 0 {
                    lean_ctor_set(v___x_3590_, 1, v___x_3611_);
                    lean_ctor_set(v___x_3590_, 0, v_a_3598_);
                    v___x_3615_ = v___x_3590_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3598_);
                    lean_ctor_set(v_reuseFailAlloc_3620_, 1, v___x_3611_);
                    v___x_3615_ = v_reuseFailAlloc_3620_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                lean_ctor_set_uint8(
                    v___x_3615_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3475_,
                );
                lean_ctor_set_uint8(
                    v___x_3615_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_3613_,
                );
                v___x_3616_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3616_, 0, v___x_3615_);
                lean_ctor_set(v___x_3616_, 1, v_body_3596_);
                if v_isShared_3605_ == 0 {
                    lean_ctor_set(v___x_3604_, 0, v___x_3616_);
                    v___x_3618_ = v___x_3604_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
                    v___x_3618_ = v_reuseFailAlloc_3619_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3618_;
            }
            26 => {
                if v_isShared_3625_ == 0 {
                    v___x_3627_ = v___x_3624_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
                    v___x_3627_ = v_reuseFailAlloc_3628_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3627_;
            }
            28 => {
                if v_isShared_3633_ == 0 {
                    v___x_3635_ = v___x_3632_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
                    v___x_3635_ = v_reuseFailAlloc_3636_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3635_;
            }
            30 => {
                if v_isShared_3641_ == 0 {
                    v___x_3643_ = v___x_3640_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3643_;
            }
            32 => {
                if v_isShared_3651_ == 0 {
                    v___x_3653_ = v___x_3650_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
                    v___x_3653_ = v_reuseFailAlloc_3654_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3653_;
            }
            34 => {
                v___x_3666_ =
                    l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_whnfToForall___redArg(
                        v_snd_3483_,
                        v_a_3468_,
                        v_a_3469_,
                        v_a_3470_,
                        v_a_3471_,
                        v_a_3472_,
                    );
                if lean_obj_tag(v___x_3666_) == 0 {
                    v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
                    lean_inc(v_a_3667_);
                    lean_dec_ref_known(v___x_3666_, 1);
                    if lean_obj_tag(v_a_3667_) == 7 {
                        v_binderType_3668_ = lean_ctor_get(v_a_3667_, 1);
                        lean_inc_ref(v_binderType_3668_);
                        v_body_3669_ = lean_ctor_get(v_a_3667_, 2);
                        lean_inc_ref(v_body_3669_);
                        lean_dec_ref_known(v_a_3667_, 3);
                        lean_inc_ref(v_e_x27_3660_);
                        lean_inc_ref(v_e_x27_3657_);
                        v___x_3670_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__0___redArg(v_e_x27_3657_, v_e_x27_3660_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                        if lean_obj_tag(v___x_3670_) == 0 {
                            v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
                            lean_inc(v_a_3671_);
                            lean_dec_ref_known(v___x_3670_, 1);
                            lean_inc_ref(v_binderType_3668_);
                            v___x_3672_ = l_Lean_Meta_Sym_getLevel___redArg(
                                v_binderType_3668_,
                                v_a_3468_,
                                v_a_3469_,
                                v_a_3470_,
                                v_a_3471_,
                                v_a_3472_,
                            );
                            if lean_obj_tag(v___x_3672_) == 0 {
                                v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
                                lean_inc(v_a_3673_);
                                lean_dec_ref_known(v___x_3672_, 1);
                                lean_inc_ref(v_body_3669_);
                                v___x_3674_ = l_Lean_Meta_Sym_getLevel___redArg(
                                    v_body_3669_,
                                    v_a_3468_,
                                    v_a_3469_,
                                    v_a_3470_,
                                    v_a_3471_,
                                    v_a_3472_,
                                );
                                if lean_obj_tag(v___x_3674_) == 0 {
                                    v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
                                    v_isSharedCheck_3694_ = (!lean_is_exclusive(v___x_3674_)) as u8;
                                    if v_isSharedCheck_3694_ == 0 {
                                        v___x_3677_ = v___x_3674_;
                                        v_isShared_3678_ = v_isSharedCheck_3694_;
                                        state = 35;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3675_);
                                        lean_dec(v___x_3674_);
                                        v___x_3677_ = lean_box(0);
                                        v_isShared_3678_ = v_isSharedCheck_3694_;
                                        state = 35;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3673_);
                                    lean_dec(v_a_3671_);
                                    lean_dec_ref(v_body_3669_);
                                    lean_dec_ref(v_binderType_3668_);
                                    lean_del_object(v___x_3664_);
                                    lean_dec_ref(v_proof_3661_);
                                    lean_dec_ref(v_e_x27_3660_);
                                    lean_dec_ref(v_proof_3658_);
                                    lean_dec_ref(v_e_x27_3657_);
                                    lean_dec_ref(v_arg_3477_);
                                    lean_dec_ref(v_fn_3476_);
                                    v_a_3695_ = lean_ctor_get(v___x_3674_, 0);
                                    v_isSharedCheck_3702_ = (!lean_is_exclusive(v___x_3674_)) as u8;
                                    if v_isSharedCheck_3702_ == 0 {
                                        v___x_3697_ = v___x_3674_;
                                        v_isShared_3698_ = v_isSharedCheck_3702_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3695_);
                                        lean_dec(v___x_3674_);
                                        v___x_3697_ = lean_box(0);
                                        v_isShared_3698_ = v_isSharedCheck_3702_;
                                        state = 39;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_3671_);
                                lean_dec_ref(v_body_3669_);
                                lean_dec_ref(v_binderType_3668_);
                                lean_del_object(v___x_3664_);
                                lean_dec_ref(v_proof_3661_);
                                lean_dec_ref(v_e_x27_3660_);
                                lean_dec_ref(v_proof_3658_);
                                lean_dec_ref(v_e_x27_3657_);
                                lean_dec_ref(v_arg_3477_);
                                lean_dec_ref(v_fn_3476_);
                                v_a_3703_ = lean_ctor_get(v___x_3672_, 0);
                                v_isSharedCheck_3710_ = (!lean_is_exclusive(v___x_3672_)) as u8;
                                if v_isSharedCheck_3710_ == 0 {
                                    v___x_3705_ = v___x_3672_;
                                    v_isShared_3706_ = v_isSharedCheck_3710_;
                                    state = 41;
                                    continue;
                                } else {
                                    lean_inc(v_a_3703_);
                                    lean_dec(v___x_3672_);
                                    v___x_3705_ = lean_box(0);
                                    v_isShared_3706_ = v_isSharedCheck_3710_;
                                    state = 41;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_body_3669_);
                            lean_dec_ref(v_binderType_3668_);
                            lean_del_object(v___x_3664_);
                            lean_dec_ref(v_proof_3661_);
                            lean_dec_ref(v_e_x27_3660_);
                            lean_dec_ref(v_proof_3658_);
                            lean_dec_ref(v_e_x27_3657_);
                            lean_dec_ref(v_arg_3477_);
                            lean_dec_ref(v_fn_3476_);
                            v_a_3711_ = lean_ctor_get(v___x_3670_, 0);
                            v_isSharedCheck_3718_ = (!lean_is_exclusive(v___x_3670_)) as u8;
                            if v_isSharedCheck_3718_ == 0 {
                                v___x_3713_ = v___x_3670_;
                                v_isShared_3714_ = v_isSharedCheck_3718_;
                                state = 43;
                                continue;
                            } else {
                                lean_inc(v_a_3711_);
                                lean_dec(v___x_3670_);
                                v___x_3713_ = lean_box(0);
                                v_isShared_3714_ = v_isSharedCheck_3718_;
                                state = 43;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3667_);
                        lean_del_object(v___x_3664_);
                        lean_dec_ref(v_proof_3661_);
                        lean_dec_ref(v_e_x27_3660_);
                        lean_dec_ref(v_proof_3658_);
                        lean_dec_ref(v_e_x27_3657_);
                        lean_dec_ref(v_arg_3477_);
                        lean_dec_ref(v_fn_3476_);
                        v___x_3719_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__6);
                        v___x_3720_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go_spec__1(v___x_3719_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
                        return v___x_3720_;
                    }
                } else {
                    lean_del_object(v___x_3664_);
                    lean_dec_ref(v_proof_3661_);
                    lean_dec_ref(v_e_x27_3660_);
                    lean_dec_ref(v_proof_3658_);
                    lean_dec_ref(v_e_x27_3657_);
                    lean_dec_ref(v_arg_3477_);
                    lean_dec_ref(v_fn_3476_);
                    v_a_3721_ = lean_ctor_get(v___x_3666_, 0);
                    v_isSharedCheck_3728_ = (!lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3728_ == 0 {
                        v___x_3723_ = v___x_3666_;
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 45;
                        continue;
                    } else {
                        lean_inc(v_a_3721_);
                        lean_dec(v___x_3666_);
                        v___x_3723_ = lean_box(0);
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 45;
                        continue;
                    }
                }
            }
            35 => {
                v___x_3679_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5;
                v___x_3680_ = lean_box(0);
                v___x_3681_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3681_, 0, v_a_3675_);
                lean_ctor_set(v___x_3681_, 1, v___x_3680_);
                v___x_3682_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3682_, 0, v_a_3673_);
                lean_ctor_set(v___x_3682_, 1, v___x_3681_);
                v___x_3683_ = l_Lean_mkConst(v___x_3679_, v___x_3682_);
                lean_inc_ref(v_body_3669_);
                v___x_3684_ = l_Lean_mkApp8(
                    v___x_3683_,
                    v_binderType_3668_,
                    v_body_3669_,
                    v_fn_3476_,
                    v_e_x27_3657_,
                    v_arg_3477_,
                    v_e_x27_3660_,
                    v_proof_3658_,
                    v_proof_3661_,
                );
                if v_contextDependent_3659_ == 0 {
                    v___y_3686_ = v_contextDependent_3662_;
                    state = 36;
                    continue;
                } else {
                    v___y_3686_ = v___x_3502_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_3665_ == 0 {
                    lean_ctor_set(v___x_3664_, 1, v___x_3684_);
                    lean_ctor_set(v___x_3664_, 0, v_a_3671_);
                    v___x_3688_ = v___x_3664_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3671_);
                    lean_ctor_set(v_reuseFailAlloc_3693_, 1, v___x_3684_);
                    v___x_3688_ = v_reuseFailAlloc_3693_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                lean_ctor_set_uint8(
                    v___x_3688_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3475_,
                );
                lean_ctor_set_uint8(
                    v___x_3688_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_3686_,
                );
                v___x_3689_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3689_, 0, v___x_3688_);
                lean_ctor_set(v___x_3689_, 1, v_body_3669_);
                if v_isShared_3678_ == 0 {
                    lean_ctor_set(v___x_3677_, 0, v___x_3689_);
                    v___x_3691_ = v___x_3677_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3691_;
            }
            39 => {
                if v_isShared_3698_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3700_;
            }
            41 => {
                if v_isShared_3706_ == 0 {
                    v___x_3708_ = v___x_3705_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
                    v___x_3708_ = v_reuseFailAlloc_3709_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3708_;
            }
            43 => {
                if v_isShared_3714_ == 0 {
                    v___x_3716_ = v___x_3713_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
                    v___x_3716_ = v_reuseFailAlloc_3717_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_3716_;
            }
            45 => {
                if v_isShared_3724_ == 0 {
                    v___x_3726_ = v___x_3723_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3726_;
            }
            47 => {
                if v_isShared_3734_ == 0 {
                    v___x_3736_ = v___x_3733_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
                    v___x_3736_ = v_reuseFailAlloc_3737_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_3736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___boxed(
    mut v_i_3744_: *mut LeanObject,
    mut v_e_3745_: *mut LeanObject,
    mut v_a_3746_: *mut LeanObject,
    mut v_a_3747_: *mut LeanObject,
    mut v_a_3748_: *mut LeanObject,
    mut v_a_3749_: *mut LeanObject,
    mut v_a_3750_: *mut LeanObject,
    mut v_a_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
    mut v_a_3754_: *mut LeanObject,
    mut v_a_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3756_: *mut LeanObject = core::ptr::null_mut();
    v_res_3756_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(
        v_i_3744_, v_e_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_,
        v_a_3752_, v_a_3753_, v_a_3754_,
    );
    lean_dec(v_a_3754_);
    lean_dec_ref(v_a_3753_);
    lean_dec(v_a_3752_);
    lean_dec_ref(v_a_3751_);
    lean_dec(v_a_3750_);
    lean_dec_ref(v_a_3749_);
    lean_dec(v_a_3748_);
    lean_dec_ref(v_a_3747_);
    lean_dec(v_a_3746_);
    lean_dec(v_i_3744_);
    return v_res_3756_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(
    mut v_n_3757_: *mut LeanObject,
    mut v_e_3758_: *mut LeanObject,
    mut v_a_3759_: *mut LeanObject,
    mut v_a_3760_: *mut LeanObject,
    mut v_a_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
    mut v_a_3763_: *mut LeanObject,
    mut v_a_3764_: *mut LeanObject,
    mut v_a_3765_: *mut LeanObject,
    mut v_a_3766_: *mut LeanObject,
    mut v_a_3767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v_fst_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut v_a_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3769_ =
                    l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go(
                        v_n_3757_, v_e_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_,
                        v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_,
                    );
                if lean_obj_tag(v___x_3769_) == 0 {
                    v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
                    v_isSharedCheck_3778_ = (!lean_is_exclusive(v___x_3769_)) as u8;
                    if v_isSharedCheck_3778_ == 0 {
                        v___x_3772_ = v___x_3769_;
                        v_isShared_3773_ = v_isSharedCheck_3778_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3770_);
                        lean_dec(v___x_3769_);
                        v___x_3772_ = lean_box(0);
                        v_isShared_3773_ = v_isSharedCheck_3778_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3779_ = lean_ctor_get(v___x_3769_, 0);
                    v_isSharedCheck_3786_ = (!lean_is_exclusive(v___x_3769_)) as u8;
                    if v_isSharedCheck_3786_ == 0 {
                        v___x_3781_ = v___x_3769_;
                        v_isShared_3782_ = v_isSharedCheck_3786_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3779_);
                        lean_dec(v___x_3769_);
                        v___x_3781_ = lean_box(0);
                        v_isShared_3782_ = v_isSharedCheck_3786_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3774_ = lean_ctor_get(v_a_3770_, 0);
                lean_inc(v_fst_3774_);
                lean_dec(v_a_3770_);
                if v_isShared_3773_ == 0 {
                    lean_ctor_set(v___x_3772_, 0, v_fst_3774_);
                    v___x_3776_ = v___x_3772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_fst_3774_);
                    v___x_3776_ = v_reuseFailAlloc_3777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3776_;
            }
            3 => {
                if v_isShared_3782_ == 0 {
                    v___x_3784_ = v___x_3781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
                    v___x_3784_ = v_reuseFailAlloc_3785_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed(
    mut v_n_3787_: *mut LeanObject,
    mut v_e_3788_: *mut LeanObject,
    mut v_a_3789_: *mut LeanObject,
    mut v_a_3790_: *mut LeanObject,
    mut v_a_3791_: *mut LeanObject,
    mut v_a_3792_: *mut LeanObject,
    mut v_a_3793_: *mut LeanObject,
    mut v_a_3794_: *mut LeanObject,
    mut v_a_3795_: *mut LeanObject,
    mut v_a_3796_: *mut LeanObject,
    mut v_a_3797_: *mut LeanObject,
    mut v_a_3798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3799_: *mut LeanObject = core::ptr::null_mut();
    v_res_3799_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(
        v_n_3787_, v_e_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_,
        v_a_3795_, v_a_3796_, v_a_3797_,
    );
    lean_dec(v_a_3797_);
    lean_dec_ref(v_a_3796_);
    lean_dec(v_a_3795_);
    lean_dec_ref(v_a_3794_);
    lean_dec(v_a_3793_);
    lean_dec_ref(v_a_3792_);
    lean_dec(v_a_3791_);
    lean_dec_ref(v_a_3790_);
    lean_dec(v_a_3789_);
    lean_dec(v_n_3787_);
    return v_res_3799_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpFixedPrefix(
    mut v_e_3800_: *mut LeanObject,
    mut v_prefixSize_3801_: *mut LeanObject,
    mut v_suffixSize_3802_: *mut LeanObject,
    mut v_a_3803_: *mut LeanObject,
    mut v_a_3804_: *mut LeanObject,
    mut v_a_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
    mut v_a_3807_: *mut LeanObject,
    mut v_a_3808_: *mut LeanObject,
    mut v_a_3809_: *mut LeanObject,
    mut v_a_3810_: *mut LeanObject,
    mut v_a_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numArgs_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    v_numArgs_3813_ = l_Lean_Expr_getAppNumArgs(v_e_3800_);
    v___x_3814_ = lean_nat_dec_le(v_numArgs_3813_, v_prefixSize_3801_);
    if v___x_3814_ == 0 {
        let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3816_: u8 = 0;
        v___x_3815_ = lean_nat_add(v_prefixSize_3801_, v_suffixSize_3802_);
        v___x_3816_ = lean_nat_dec_lt(v___x_3815_, v_numArgs_3813_);
        lean_dec(v___x_3815_);
        if v___x_3816_ == 0 {
            let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_suffixSize_3802_);
            v___x_3817_ = lean_nat_sub(v_numArgs_3813_, v_prefixSize_3801_);
            lean_dec(v_numArgs_3813_);
            v___x_3818_ =
                l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main(
                    v___x_3817_,
                    v_e_3800_,
                    v_a_3803_,
                    v_a_3804_,
                    v_a_3805_,
                    v_a_3806_,
                    v_a_3807_,
                    v_a_3808_,
                    v_a_3809_,
                    v_a_3810_,
                    v_a_3811_,
                );
            lean_dec(v___x_3817_);
            return v___x_3818_;
        } else {
            let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
            v___x_3819_ = lean_nat_sub(v_numArgs_3813_, v_prefixSize_3801_);
            lean_dec(v_numArgs_3813_);
            v___x_3820_ = lean_nat_sub(v___x_3819_, v_suffixSize_3802_);
            lean_dec(v___x_3819_);
            v___x_3821_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_main___boxed as *mut core::ffi::c_void, 12, 1);
            lean_closure_set(v___x_3821_, 0, v_suffixSize_3802_);
            v___x_3822_ =
                l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(
                    v___x_3821_,
                    v_e_3800_,
                    v___x_3820_,
                    v_a_3803_,
                    v_a_3804_,
                    v_a_3805_,
                    v_a_3806_,
                    v_a_3807_,
                    v_a_3808_,
                    v_a_3809_,
                    v_a_3810_,
                    v_a_3811_,
                );
            lean_dec(v___x_3820_);
            return v___x_3822_;
        }
    } else {
        let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_numArgs_3813_);
        lean_dec(v_suffixSize_3802_);
        lean_dec_ref(v_e_3800_);
        v___x_3823_ =
            l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
        v___x_3824_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3824_, 0, v___x_3823_);
        return v___x_3824_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpFixedPrefix___boxed(
    mut v_e_3825_: *mut LeanObject,
    mut v_prefixSize_3826_: *mut LeanObject,
    mut v_suffixSize_3827_: *mut LeanObject,
    mut v_a_3828_: *mut LeanObject,
    mut v_a_3829_: *mut LeanObject,
    mut v_a_3830_: *mut LeanObject,
    mut v_a_3831_: *mut LeanObject,
    mut v_a_3832_: *mut LeanObject,
    mut v_a_3833_: *mut LeanObject,
    mut v_a_3834_: *mut LeanObject,
    mut v_a_3835_: *mut LeanObject,
    mut v_a_3836_: *mut LeanObject,
    mut v_a_3837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3838_: *mut LeanObject = core::ptr::null_mut();
    v_res_3838_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(
        v_e_3825_,
        v_prefixSize_3826_,
        v_suffixSize_3827_,
        v_a_3828_,
        v_a_3829_,
        v_a_3830_,
        v_a_3831_,
        v_a_3832_,
        v_a_3833_,
        v_a_3834_,
        v_a_3835_,
        v_a_3836_,
    );
    lean_dec(v_a_3836_);
    lean_dec_ref(v_a_3835_);
    lean_dec(v_a_3834_);
    lean_dec_ref(v_a_3833_);
    lean_dec(v_a_3832_);
    lean_dec_ref(v_a_3831_);
    lean_dec(v_a_3830_);
    lean_dec_ref(v_a_3829_);
    lean_dec(v_a_3828_);
    lean_dec(v_prefixSize_3826_);
    return v_res_3838_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    v___x_3840_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_3841_ = lean_unsigned_to_nat(13);
    v___x_3842_ = lean_unsigned_to_nat(308);
    v___x_3843_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__0;
    v___x_3844_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_3845_ = l_mkPanicMessageWithDecl(
        v___x_3844_,
        v___x_3843_,
        v___x_3842_,
        v___x_3841_,
        v___x_3840_,
    );
    return v___x_3845_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(
    mut v_rewritable_3846_: *mut LeanObject,
    mut v_i_3847_: *mut LeanObject,
    mut v_e_3848_: *mut LeanObject,
    mut v_a_3849_: *mut LeanObject,
    mut v_a_3850_: *mut LeanObject,
    mut v_a_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
    mut v_a_3853_: *mut LeanObject,
    mut v_a_3854_: *mut LeanObject,
    mut v_a_3855_: *mut LeanObject,
    mut v_a_3856_: *mut LeanObject,
    mut v_a_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: u8 = 0;
    let mut v_fn_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3869_: u8 = 0;
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: u8 = 0;
    let mut v_contextDependent_3872_: u8 = 0;
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3879_: u8 = 0;
    let mut v___x_3880_: u8 = 0;
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3885_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3859_ = lean_unsigned_to_nat(0);
                v___x_3860_ = lean_nat_dec_eq(v_i_3847_, v___x_3859_);
                if v___x_3860_ == 0 {
                    if lean_obj_tag(v_e_3848_) == 5 {
                        v_fn_3861_ = lean_ctor_get(v_e_3848_, 0);
                        lean_inc_ref_n(v_fn_3861_, 2);
                        v_arg_3862_ = lean_ctor_get(v_e_3848_, 1);
                        lean_inc_ref(v_arg_3862_);
                        v___x_3863_ = lean_unsigned_to_nat(1);
                        v___x_3864_ = lean_nat_sub(v_i_3847_, v___x_3863_);
                        v___x_3865_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(v_rewritable_3846_, v___x_3864_, v_fn_3861_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
                        if lean_obj_tag(v___x_3865_) == 0 {
                            v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
                            v_isSharedCheck_3885_ = (!lean_is_exclusive(v___x_3865_)) as u8;
                            if v_isSharedCheck_3885_ == 0 {
                                v___x_3868_ = v___x_3865_;
                                v_isShared_3869_ = v_isSharedCheck_3885_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3866_);
                                lean_dec(v___x_3865_);
                                v___x_3868_ = lean_box(0);
                                v_isShared_3869_ = v_isSharedCheck_3885_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3864_);
                            lean_dec_ref(v_arg_3862_);
                            lean_dec_ref_known(v_e_3848_, 2);
                            lean_dec_ref(v_fn_3861_);
                            return v___x_3865_;
                        }
                    } else {
                        lean_dec_ref(v_e_3848_);
                        v___x_3886_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___closed__1);
                        v___x_3887_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_3886_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
                        return v___x_3887_;
                    }
                } else {
                    lean_dec_ref(v_e_3848_);
                    v___x_3888_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
                    v___x_3889_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3889_, 0, v___x_3888_);
                    return v___x_3889_;
                }
            }
            1 => {
                v___x_3870_ = lean_array_fget_borrowed(v_rewritable_3846_, v___x_3864_);
                lean_dec(v___x_3864_);
                v___x_3871_ = (lean_unbox(v___x_3870_) as u8);
                if v___x_3871_ == 0 {
                    if lean_obj_tag(v_a_3866_) == 0 {
                        lean_dec_ref(v_arg_3862_);
                        lean_dec_ref_known(v_e_3848_, 2);
                        lean_dec_ref(v_fn_3861_);
                        v_contextDependent_3872_ = lean_ctor_get_uint8(v_a_3866_, 1 as u32);
                        lean_dec_ref_known(v_a_3866_, 0);
                        v___x_3873_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_3872_);
                        if v_isShared_3869_ == 0 {
                            lean_ctor_set(v___x_3868_, 0, v___x_3873_);
                            v___x_3875_ = v___x_3868_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
                            v___x_3875_ = v_reuseFailAlloc_3876_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3868_);
                        v_e_x27_3877_ = lean_ctor_get(v_a_3866_, 0);
                        lean_inc_ref(v_e_x27_3877_);
                        v_proof_3878_ = lean_ctor_get(v_a_3866_, 1);
                        lean_inc_ref(v_proof_3878_);
                        v_contextDependent_3879_ = lean_ctor_get_uint8(
                            v_a_3866_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        lean_dec_ref_known(v_a_3866_, 2);
                        v___x_3880_ = (lean_unbox(v___x_3870_) as u8);
                        v___x_3881_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_3848_, v_fn_3861_, v_arg_3862_, v_e_x27_3877_, v_proof_3878_, v___x_3880_, v_contextDependent_3879_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
                        return v___x_3881_;
                    }
                } else {
                    lean_del_object(v___x_3868_);
                    lean_inc(v_a_3857_);
                    lean_inc_ref(v_a_3856_);
                    lean_inc(v_a_3855_);
                    lean_inc_ref(v_a_3854_);
                    lean_inc(v_a_3853_);
                    lean_inc_ref(v_a_3852_);
                    lean_inc(v_a_3851_);
                    lean_inc_ref(v_a_3850_);
                    lean_inc(v_a_3849_);
                    lean_inc_ref(v_arg_3862_);
                    v___x_3882_ = lean_sym_simp(
                        v_arg_3862_,
                        v_a_3849_,
                        v_a_3850_,
                        v_a_3851_,
                        v_a_3852_,
                        v_a_3853_,
                        v_a_3854_,
                        v_a_3855_,
                        v_a_3856_,
                        v_a_3857_,
                    );
                    if lean_obj_tag(v___x_3882_) == 0 {
                        v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
                        lean_inc(v_a_3883_);
                        lean_dec_ref_known(v___x_3882_, 1);
                        v___x_3884_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(
                            v_e_3848_,
                            v_fn_3861_,
                            v_arg_3862_,
                            v_a_3866_,
                            v_a_3883_,
                            v_a_3852_,
                            v_a_3853_,
                            v_a_3854_,
                            v_a_3855_,
                            v_a_3856_,
                            v_a_3857_,
                        );
                        return v___x_3884_;
                    } else {
                        lean_dec(v_a_3866_);
                        lean_dec_ref(v_arg_3862_);
                        lean_dec_ref(v_fn_3861_);
                        lean_dec_ref_known(v_e_3848_, 2);
                        return v___x_3882_;
                    }
                }
            }
            2 => {
                return v___x_3875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg___boxed(
    mut v_rewritable_3890_: *mut LeanObject,
    mut v_i_3891_: *mut LeanObject,
    mut v_e_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
    mut v_a_3894_: *mut LeanObject,
    mut v_a_3895_: *mut LeanObject,
    mut v_a_3896_: *mut LeanObject,
    mut v_a_3897_: *mut LeanObject,
    mut v_a_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3903_: *mut LeanObject = core::ptr::null_mut();
    v_res_3903_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(
            v_rewritable_3890_,
            v_i_3891_,
            v_e_3892_,
            v_a_3893_,
            v_a_3894_,
            v_a_3895_,
            v_a_3896_,
            v_a_3897_,
            v_a_3898_,
            v_a_3899_,
            v_a_3900_,
            v_a_3901_,
        );
    lean_dec(v_a_3901_);
    lean_dec_ref(v_a_3900_);
    lean_dec(v_a_3899_);
    lean_dec_ref(v_a_3898_);
    lean_dec(v_a_3897_);
    lean_dec_ref(v_a_3896_);
    lean_dec(v_a_3895_);
    lean_dec_ref(v_a_3894_);
    lean_dec(v_a_3893_);
    lean_dec(v_i_3891_);
    lean_dec_ref(v_rewritable_3890_);
    return v_res_3903_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(
    mut v_rewritable_3904_: *mut LeanObject,
    mut v_i_3905_: *mut LeanObject,
    mut v_e_3906_: *mut LeanObject,
    mut v_h_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
    mut v_a_3909_: *mut LeanObject,
    mut v_a_3910_: *mut LeanObject,
    mut v_a_3911_: *mut LeanObject,
    mut v_a_3912_: *mut LeanObject,
    mut v_a_3913_: *mut LeanObject,
    mut v_a_3914_: *mut LeanObject,
    mut v_a_3915_: *mut LeanObject,
    mut v_a_3916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    v___x_3918_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(
            v_rewritable_3904_,
            v_i_3905_,
            v_e_3906_,
            v_a_3908_,
            v_a_3909_,
            v_a_3910_,
            v_a_3911_,
            v_a_3912_,
            v_a_3913_,
            v_a_3914_,
            v_a_3915_,
            v_a_3916_,
        );
    return v___x_3918_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___boxed(
    mut v_rewritable_3919_: *mut LeanObject,
    mut v_i_3920_: *mut LeanObject,
    mut v_e_3921_: *mut LeanObject,
    mut v_h_3922_: *mut LeanObject,
    mut v_a_3923_: *mut LeanObject,
    mut v_a_3924_: *mut LeanObject,
    mut v_a_3925_: *mut LeanObject,
    mut v_a_3926_: *mut LeanObject,
    mut v_a_3927_: *mut LeanObject,
    mut v_a_3928_: *mut LeanObject,
    mut v_a_3929_: *mut LeanObject,
    mut v_a_3930_: *mut LeanObject,
    mut v_a_3931_: *mut LeanObject,
    mut v_a_3932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3933_: *mut LeanObject = core::ptr::null_mut();
    v_res_3933_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go(
        v_rewritable_3919_,
        v_i_3920_,
        v_e_3921_,
        v_h_3922_,
        v_a_3923_,
        v_a_3924_,
        v_a_3925_,
        v_a_3926_,
        v_a_3927_,
        v_a_3928_,
        v_a_3929_,
        v_a_3930_,
        v_a_3931_,
    );
    lean_dec(v_a_3931_);
    lean_dec_ref(v_a_3930_);
    lean_dec(v_a_3929_);
    lean_dec_ref(v_a_3928_);
    lean_dec(v_a_3927_);
    lean_dec_ref(v_a_3926_);
    lean_dec(v_a_3925_);
    lean_dec_ref(v_a_3924_);
    lean_dec(v_a_3923_);
    lean_dec(v_i_3920_);
    lean_dec_ref(v_rewritable_3919_);
    return v_res_3933_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(
    mut v_rewritable_3934_: *mut LeanObject,
    mut v___x_3935_: *mut LeanObject,
    mut v_x_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
    mut v___y_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
    mut v___y_3941_: *mut LeanObject,
    mut v___y_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    v___x_3947_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(
            v_rewritable_3934_,
            v___x_3935_,
            v_x_3936_,
            v___y_3937_,
            v___y_3938_,
            v___y_3939_,
            v___y_3940_,
            v___y_3941_,
            v___y_3942_,
            v___y_3943_,
            v___y_3944_,
            v___y_3945_,
        );
    return v___x_3947_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed(
    mut v_rewritable_3948_: *mut LeanObject,
    mut v___x_3949_: *mut LeanObject,
    mut v_x_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
    mut v___y_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
    mut v___y_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3961_: *mut LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0(
        v_rewritable_3948_,
        v___x_3949_,
        v_x_3950_,
        v___y_3951_,
        v___y_3952_,
        v___y_3953_,
        v___y_3954_,
        v___y_3955_,
        v___y_3956_,
        v___y_3957_,
        v___y_3958_,
        v___y_3959_,
    );
    lean_dec(v___y_3959_);
    lean_dec_ref(v___y_3958_);
    lean_dec(v___y_3957_);
    lean_dec_ref(v___y_3956_);
    lean_dec(v___y_3955_);
    lean_dec_ref(v___y_3954_);
    lean_dec(v___y_3953_);
    lean_dec_ref(v___y_3952_);
    lean_dec(v___y_3951_);
    lean_dec(v___x_3949_);
    lean_dec_ref(v_rewritable_3948_);
    return v_res_3961_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpInterlaced(
    mut v_e_3962_: *mut LeanObject,
    mut v_rewritable_3963_: *mut LeanObject,
    mut v_a_3964_: *mut LeanObject,
    mut v_a_3965_: *mut LeanObject,
    mut v_a_3966_: *mut LeanObject,
    mut v_a_3967_: *mut LeanObject,
    mut v_a_3968_: *mut LeanObject,
    mut v_a_3969_: *mut LeanObject,
    mut v_a_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numArgs_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: u8 = 0;
    v_numArgs_3974_ = l_Lean_Expr_getAppNumArgs(v_e_3962_);
    v___x_3975_ = lean_unsigned_to_nat(0);
    v___x_3976_ = lean_nat_dec_eq(v_numArgs_3974_, v___x_3975_);
    if v___x_3976_ == 0 {
        let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3978_: u8 = 0;
        v___x_3977_ = lean_array_get_size(v_rewritable_3963_);
        v___x_3978_ = lean_nat_dec_lt(v___x_3977_, v_numArgs_3974_);
        if v___x_3978_ == 0 {
            let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
            v___x_3979_ =
                l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpInterlaced_go___redArg(
                    v_rewritable_3963_,
                    v_numArgs_3974_,
                    v_e_3962_,
                    v_a_3964_,
                    v_a_3965_,
                    v_a_3966_,
                    v_a_3967_,
                    v_a_3968_,
                    v_a_3969_,
                    v_a_3970_,
                    v_a_3971_,
                    v_a_3972_,
                );
            lean_dec(v_numArgs_3974_);
            lean_dec_ref(v_rewritable_3963_);
            return v___x_3979_;
        } else {
            let mut v___f_3980_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
            v___f_3980_ = lean_alloc_closure(
                l_Lean_Meta_Sym_Simp_simpInterlaced___lam__0___boxed as *mut core::ffi::c_void,
                13,
                2,
            );
            lean_closure_set(v___f_3980_, 0, v_rewritable_3963_);
            lean_closure_set(v___f_3980_, 1, v___x_3977_);
            v___x_3981_ = lean_nat_sub(v_numArgs_3974_, v___x_3977_);
            lean_dec(v_numArgs_3974_);
            v___x_3982_ =
                l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(
                    v___f_3980_,
                    v_e_3962_,
                    v___x_3981_,
                    v_a_3964_,
                    v_a_3965_,
                    v_a_3966_,
                    v_a_3967_,
                    v_a_3968_,
                    v_a_3969_,
                    v_a_3970_,
                    v_a_3971_,
                    v_a_3972_,
                );
            lean_dec(v___x_3981_);
            return v___x_3982_;
        }
    } else {
        let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_numArgs_3974_);
        lean_dec_ref(v_rewritable_3963_);
        lean_dec_ref(v_e_3962_);
        v___x_3983_ =
            l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
        v___x_3984_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3984_, 0, v___x_3983_);
        return v___x_3984_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpInterlaced___boxed(
    mut v_e_3985_: *mut LeanObject,
    mut v_rewritable_3986_: *mut LeanObject,
    mut v_a_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
    mut v_a_3989_: *mut LeanObject,
    mut v_a_3990_: *mut LeanObject,
    mut v_a_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
    mut v_a_3993_: *mut LeanObject,
    mut v_a_3994_: *mut LeanObject,
    mut v_a_3995_: *mut LeanObject,
    mut v_a_3996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3997_: *mut LeanObject = core::ptr::null_mut();
    v_res_3997_ = l_Lean_Meta_Sym_Simp_simpInterlaced(
        v_e_3985_,
        v_rewritable_3986_,
        v_a_3987_,
        v_a_3988_,
        v_a_3989_,
        v_a_3990_,
        v_a_3991_,
        v_a_3992_,
        v_a_3993_,
        v_a_3994_,
        v_a_3995_,
    );
    lean_dec(v_a_3995_);
    lean_dec_ref(v_a_3994_);
    lean_dec(v_a_3993_);
    lean_dec_ref(v_a_3992_);
    lean_dec(v_a_3991_);
    lean_dec_ref(v_a_3990_);
    lean_dec(v_a_3989_);
    lean_dec_ref(v_a_3988_);
    lean_dec(v_a_3987_);
    return v_res_3997_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(
    mut v_argResults_3998_: *mut LeanObject,
    mut v_numEqs_3999_: *mut LeanObject,
    mut v_result_4000_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_result_4000_) == 0 {
        let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4003_: u8 = 0;
        lean_dec(v_numEqs_3999_);
        v___x_4001_ = lean_unsigned_to_nat(0);
        v___x_4002_ = lean_array_get_size(v_argResults_3998_);
        v___x_4003_ = lean_nat_dec_lt(v___x_4001_, v___x_4002_);
        if v___x_4003_ == 0 {
            lean_dec_ref_known(v_result_4000_, 0);
            return v_argResults_3998_;
        } else {
            let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
            v___x_4004_ = lean_array_push(v_argResults_3998_, v_result_4000_);
            return v___x_4004_;
        }
    } else {
        let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4006_: u8 = 0;
        v___x_4005_ = lean_array_get_size(v_argResults_3998_);
        v___x_4006_ = lean_nat_dec_lt(v___x_4005_, v_numEqs_3999_);
        if v___x_4006_ == 0 {
            let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_numEqs_3999_);
            v___x_4007_ = lean_array_push(v_argResults_3998_, v_result_4000_);
            return v___x_4007_;
        } else {
            let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_argResults_3998_);
            v___x_4008_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
            v___x_4009_ = lean_mk_array(v_numEqs_3999_, v___x_4008_);
            v___x_4010_ = lean_array_push(v___x_4009_, v_result_4000_);
            return v___x_4010_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1()
-> *mut LeanObject {
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    v___x_4012_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_4013_ = lean_unsigned_to_nat(13);
    v___x_4014_ = lean_unsigned_to_nat(429);
    v___x_4015_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__0;
    v___x_4016_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_4017_ = l_mkPanicMessageWithDecl(
        v___x_4016_,
        v___x_4015_,
        v___x_4014_,
        v___x_4013_,
        v___x_4012_,
    );
    return v___x_4017_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(
    mut v_argKinds_4018_: *mut LeanObject,
    mut v_mkNonRflResult_4019_: *mut LeanObject,
    mut v_e_4020_: *mut LeanObject,
    mut v_i_4021_: *mut LeanObject,
    mut v_numEqs_4022_: *mut LeanObject,
    mut v_argResults_4023_: *mut LeanObject,
    mut v_anyCD_4024_: u8,
    mut v_a_4025_: *mut LeanObject,
    mut v_a_4026_: *mut LeanObject,
    mut v_a_4027_: *mut LeanObject,
    mut v_a_4028_: *mut LeanObject,
    mut v_a_4029_: *mut LeanObject,
    mut v_a_4030_: *mut LeanObject,
    mut v_a_4031_: *mut LeanObject,
    mut v_a_4032_: *mut LeanObject,
    mut v_a_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4060_: u8 = 0;
    let mut v_contextDependent_4062_: u8 = 0;
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: u8 = 0;
    let mut v_contextDependent_4078_: u8 = 0;
    let mut v_contextDependent_4079_: u8 = 0;
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_4020_) == 5 {
                    v_fn_4035_ = lean_ctor_get(v_e_4020_, 0);
                    lean_inc_ref(v_fn_4035_);
                    v_arg_4036_ = lean_ctor_get(v_e_4020_, 1);
                    lean_inc_ref(v_arg_4036_);
                    lean_dec_ref_known(v_e_4020_, 2);
                    v___x_4050_ = 0;
                    v___x_4051_ = lean_box((v___x_4050_) as usize);
                    v___x_4052_ = lean_array_get(v___x_4051_, v_argKinds_4018_, v_i_4021_);
                    lean_dec(v___x_4051_);
                    v___x_4053_ = (lean_unbox(v___x_4052_) as u8);
                    lean_dec(v___x_4052_);
                    match v___x_4053_ {
                        5 => {
                            lean_dec_ref(v_arg_4036_);
                            v___y_4038_ = v_a_4025_;
                            v___y_4039_ = v_a_4026_;
                            v___y_4040_ = v_a_4027_;
                            v___y_4041_ = v_a_4028_;
                            v___y_4042_ = v_a_4029_;
                            v___y_4043_ = v_a_4030_;
                            v___y_4044_ = v_a_4031_;
                            v___y_4045_ = v_a_4032_;
                            v___y_4046_ = v_a_4033_;
                            state = 1;
                            continue;
                        }
                        0 => {
                            lean_dec_ref(v_arg_4036_);
                            v___y_4038_ = v_a_4025_;
                            v___y_4039_ = v_a_4026_;
                            v___y_4040_ = v_a_4027_;
                            v___y_4041_ = v_a_4028_;
                            v___y_4042_ = v_a_4029_;
                            v___y_4043_ = v_a_4030_;
                            v___y_4044_ = v_a_4031_;
                            v___y_4045_ = v_a_4032_;
                            v___y_4046_ = v_a_4033_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            lean_dec_ref(v_arg_4036_);
                            v___y_4038_ = v_a_4025_;
                            v___y_4039_ = v_a_4026_;
                            v___y_4040_ = v_a_4027_;
                            v___y_4041_ = v_a_4028_;
                            v___y_4042_ = v_a_4029_;
                            v___y_4043_ = v_a_4030_;
                            v___y_4044_ = v_a_4031_;
                            v___y_4045_ = v_a_4032_;
                            v___y_4046_ = v_a_4033_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            lean_inc(v_a_4033_);
                            lean_inc_ref(v_a_4032_);
                            lean_inc(v_a_4031_);
                            lean_inc_ref(v_a_4030_);
                            lean_inc(v_a_4029_);
                            lean_inc_ref(v_a_4028_);
                            lean_inc(v_a_4027_);
                            lean_inc_ref(v_a_4026_);
                            lean_inc(v_a_4025_);
                            v___x_4054_ = lean_sym_simp(
                                v_arg_4036_,
                                v_a_4025_,
                                v_a_4026_,
                                v_a_4027_,
                                v_a_4028_,
                                v_a_4029_,
                                v_a_4030_,
                                v_a_4031_,
                                v_a_4032_,
                                v_a_4033_,
                            );
                            if lean_obj_tag(v___x_4054_) == 0 {
                                v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
                                lean_inc_n(v_a_4055_, 2);
                                lean_dec_ref_known(v___x_4054_, 1);
                                v___x_4056_ = lean_unsigned_to_nat(1);
                                v___x_4057_ = lean_nat_sub(v_i_4021_, v___x_4056_);
                                lean_dec(v_i_4021_);
                                v___x_4058_ = lean_nat_add(v_numEqs_4022_, v___x_4056_);
                                v___x_4059_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_pushResult(v_argResults_4023_, v_numEqs_4022_, v_a_4055_);
                                if v_anyCD_4024_ == 0 {
                                    if lean_obj_tag(v_a_4055_) == 0 {
                                        v_contextDependent_4060_ =
                                            lean_ctor_get_uint8(v_a_4055_, 1 as u32);
                                        lean_dec_ref_known(v_a_4055_, 0);
                                        v_e_4020_ = v_fn_4035_;
                                        v_i_4021_ = v___x_4057_;
                                        v_numEqs_4022_ = v___x_4058_;
                                        v_argResults_4023_ = v___x_4059_;
                                        v_anyCD_4024_ = v_contextDependent_4060_;
                                        state = 0;
                                        continue;
                                    } else {
                                        v_contextDependent_4062_ = lean_ctor_get_uint8(
                                            v_a_4055_,
                                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                as u32,
                                        );
                                        lean_dec_ref_known(v_a_4055_, 2);
                                        v_e_4020_ = v_fn_4035_;
                                        v_i_4021_ = v___x_4057_;
                                        v_numEqs_4022_ = v___x_4058_;
                                        v_argResults_4023_ = v___x_4059_;
                                        v_anyCD_4024_ = v_contextDependent_4062_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4055_);
                                    v_e_4020_ = v_fn_4035_;
                                    v_i_4021_ = v___x_4057_;
                                    v_numEqs_4022_ = v___x_4058_;
                                    v_argResults_4023_ = v___x_4059_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_fn_4035_);
                                lean_dec_ref(v_argResults_4023_);
                                lean_dec(v_numEqs_4022_);
                                lean_dec(v_i_4021_);
                                lean_dec_ref(v_mkNonRflResult_4019_);
                                return v___x_4054_;
                            }
                        }
                        _ => {
                            lean_dec_ref(v_arg_4036_);
                            lean_dec_ref(v_fn_4035_);
                            lean_dec_ref(v_argResults_4023_);
                            lean_dec(v_numEqs_4022_);
                            lean_dec(v_i_4021_);
                            lean_dec_ref(v_mkNonRflResult_4019_);
                            v___x_4065_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___closed__1);
                            v___x_4066_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_4065_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
                            return v___x_4066_;
                        }
                    }
                } else {
                    lean_dec(v_numEqs_4022_);
                    lean_dec(v_i_4021_);
                    lean_dec_ref(v_e_4020_);
                    v___x_4067_ = lean_array_get_size(v_argResults_4023_);
                    v___x_4068_ = lean_unsigned_to_nat(0);
                    v___x_4069_ = lean_nat_dec_eq(v___x_4067_, v___x_4068_);
                    if v___x_4069_ == 0 {
                        v___x_4070_ = l_Array_reverse___redArg(v_argResults_4023_);
                        lean_inc(v_a_4033_);
                        lean_inc_ref(v_a_4032_);
                        lean_inc(v_a_4031_);
                        lean_inc_ref(v_a_4030_);
                        lean_inc(v_a_4029_);
                        lean_inc_ref(v_a_4028_);
                        lean_inc(v_a_4027_);
                        lean_inc_ref(v_a_4026_);
                        lean_inc(v_a_4025_);
                        v___x_4071_ = lean_apply_11(
                            v_mkNonRflResult_4019_,
                            v___x_4070_,
                            v_a_4025_,
                            v_a_4026_,
                            v_a_4027_,
                            v_a_4028_,
                            v_a_4029_,
                            v_a_4030_,
                            v_a_4031_,
                            v_a_4032_,
                            v_a_4033_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_4071_) == 0 {
                            v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
                            lean_inc(v_a_4072_);
                            if v_anyCD_4024_ == 0 {
                                lean_dec(v_a_4072_);
                                return v___x_4071_;
                            } else {
                                if lean_obj_tag(v_a_4072_) == 0 {
                                    v_contextDependent_4078_ =
                                        lean_ctor_get_uint8(v_a_4072_, 1 as u32);
                                    v___y_4077_ = v_contextDependent_4078_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_contextDependent_4079_ = lean_ctor_get_uint8(
                                        v_a_4072_,
                                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                                    );
                                    v___y_4077_ = v_contextDependent_4079_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_4071_;
                        }
                    } else {
                        lean_dec_ref(v_argResults_4023_);
                        lean_dec_ref(v_mkNonRflResult_4019_);
                        v___x_4080_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_anyCD_4024_);
                        v___x_4081_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4081_, 0, v___x_4080_);
                        return v___x_4081_;
                    }
                }
            }
            1 => {
                v___x_4047_ = lean_unsigned_to_nat(1);
                v___x_4048_ = lean_nat_sub(v_i_4021_, v___x_4047_);
                lean_dec(v_i_4021_);
                v_e_4020_ = v_fn_4035_;
                v_i_4021_ = v___x_4048_;
                v_a_4025_ = v___y_4038_;
                v_a_4026_ = v___y_4039_;
                v_a_4027_ = v___y_4040_;
                v_a_4028_ = v___y_4041_;
                v_a_4029_ = v___y_4042_;
                v_a_4030_ = v___y_4043_;
                v_a_4031_ = v___y_4044_;
                v_a_4032_ = v___y_4045_;
                v_a_4033_ = v___y_4046_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4074_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4072_);
                v___x_4075_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4075_, 0, v___x_4074_);
                return v___x_4075_;
            }
            3 => {
                if v___y_4077_ == 0 {
                    lean_dec_ref_known(v___x_4071_, 1);
                    state = 2;
                    continue;
                } else {
                    if v___x_4069_ == 0 {
                        lean_dec(v_a_4072_);
                        return v___x_4071_;
                    } else {
                        lean_dec_ref_known(v___x_4071_, 1);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_argKinds_4082_: *mut LeanObject = *_args.add(0);
    let mut v_mkNonRflResult_4083_: *mut LeanObject = *_args.add(1);
    let mut v_e_4084_: *mut LeanObject = *_args.add(2);
    let mut v_i_4085_: *mut LeanObject = *_args.add(3);
    let mut v_numEqs_4086_: *mut LeanObject = *_args.add(4);
    let mut v_argResults_4087_: *mut LeanObject = *_args.add(5);
    let mut v_anyCD_4088_: *mut LeanObject = *_args.add(6);
    let mut v_a_4089_: *mut LeanObject = *_args.add(7);
    let mut v_a_4090_: *mut LeanObject = *_args.add(8);
    let mut v_a_4091_: *mut LeanObject = *_args.add(9);
    let mut v_a_4092_: *mut LeanObject = *_args.add(10);
    let mut v_a_4093_: *mut LeanObject = *_args.add(11);
    let mut v_a_4094_: *mut LeanObject = *_args.add(12);
    let mut v_a_4095_: *mut LeanObject = *_args.add(13);
    let mut v_a_4096_: *mut LeanObject = *_args.add(14);
    let mut v_a_4097_: *mut LeanObject = *_args.add(15);
    let mut v_a_4098_: *mut LeanObject = *_args.add(16);
    let mut v_anyCD_boxed_4099_: u8 = 0;
    let mut v_res_4100_: *mut LeanObject = core::ptr::null_mut();
    v_anyCD_boxed_4099_ = (lean_unbox(v_anyCD_4088_) as u8);
    v_res_4100_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(
            v_argKinds_4082_,
            v_mkNonRflResult_4083_,
            v_e_4084_,
            v_i_4085_,
            v_numEqs_4086_,
            v_argResults_4087_,
            v_anyCD_boxed_4099_,
            v_a_4089_,
            v_a_4090_,
            v_a_4091_,
            v_a_4092_,
            v_a_4093_,
            v_a_4094_,
            v_a_4095_,
            v_a_4096_,
            v_a_4097_,
        );
    lean_dec(v_a_4097_);
    lean_dec_ref(v_a_4096_);
    lean_dec(v_a_4095_);
    lean_dec_ref(v_a_4094_);
    lean_dec(v_a_4093_);
    lean_dec_ref(v_a_4092_);
    lean_dec(v_a_4091_);
    lean_dec_ref(v_a_4090_);
    lean_dec(v_a_4089_);
    lean_dec_ref(v_argKinds_4082_);
    return v_res_4100_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    v___x_4101_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
    return v___x_4101_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(
    mut v_msg_4102_: *mut LeanObject,
    mut v___y_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_21488__overap_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    v___x_4113_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___closed__0);
    v___x_21488__overap_4114_ = lean_panic_fn_borrowed(v___x_4113_, v_msg_4102_);
    lean_inc(v___y_4111_);
    lean_inc_ref(v___y_4110_);
    lean_inc(v___y_4109_);
    lean_inc_ref(v___y_4108_);
    lean_inc(v___y_4107_);
    lean_inc_ref(v___y_4106_);
    lean_inc(v___y_4105_);
    lean_inc_ref(v___y_4104_);
    lean_inc(v___y_4103_);
    v___x_4115_ = lean_apply_10(
        v___x_21488__overap_4114_,
        v___y_4103_,
        v___y_4104_,
        v___y_4105_,
        v___y_4106_,
        v___y_4107_,
        v___y_4108_,
        v___y_4109_,
        v___y_4110_,
        v___y_4111_,
        lean_box(0),
    );
    return v___x_4115_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0___boxed(
    mut v_msg_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
    mut v___y_4123_: *mut LeanObject,
    mut v___y_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4127_: *mut LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v_msg_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
    lean_dec(v___y_4125_);
    lean_dec_ref(v___y_4124_);
    lean_dec(v___y_4123_);
    lean_dec_ref(v___y_4122_);
    lean_dec(v___y_4121_);
    lean_dec_ref(v___y_4120_);
    lean_dec(v___y_4119_);
    lean_dec_ref(v___y_4118_);
    lean_dec(v___y_4117_);
    return v_res_4127_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(
    mut v___x_4128_: u8,
    mut v_as_4129_: *mut LeanObject,
    mut v_i_4130_: usize,
    mut v_stop_4131_: usize,
) -> u8 {
    let mut v___x_4132_: u8 = 0;
    let mut v___x_4133_: u8 = 0;
    let mut v___y_4135_: u8 = 0;
    let mut v___x_4136_: usize = 0;
    let mut v___x_4137_: usize = 0;
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4132_ = lean_usize_dec_eq(v_i_4130_, v_stop_4131_);
                if v___x_4132_ == 0 {
                    v___x_4133_ = 1;
                    v___x_4139_ = lean_array_uget_borrowed(v_as_4129_, v_i_4130_);
                    v___x_4140_ = (lean_unbox(v___x_4139_) as u8);
                    if v___x_4140_ == 3 {
                        v___y_4135_ = v___x_4128_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4135_ = v___x_4132_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4141_ = 0;
                    return v___x_4141_;
                }
            }
            1 => {
                if v___y_4135_ == 0 {
                    v___x_4136_ = 1usize;
                    v___x_4137_ = lean_usize_add(v_i_4130_, v___x_4136_);
                    v_i_4130_ = v___x_4137_;
                    state = 0;
                    continue;
                } else {
                    return v___x_4133_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3___boxed(
    mut v___x_4142_: *mut LeanObject,
    mut v_as_4143_: *mut LeanObject,
    mut v_i_4144_: *mut LeanObject,
    mut v_stop_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_23297__boxed_4146_: u8 = 0;
    let mut v_i_boxed_4147_: usize = 0;
    let mut v_stop_boxed_4148_: usize = 0;
    let mut v_res_4149_: u8 = 0;
    let mut v_r_4150_: *mut LeanObject = core::ptr::null_mut();
    v___x_23297__boxed_4146_ = (lean_unbox(v___x_4142_) as u8);
    v_i_boxed_4147_ = lean_unbox_usize(v_i_4144_);
    lean_dec(v_i_4144_);
    v_stop_boxed_4148_ = lean_unbox_usize(v_stop_4145_);
    lean_dec(v_stop_4145_);
    v_res_4149_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_23297__boxed_4146_, v_as_4143_, v_i_boxed_4147_, v_stop_boxed_4148_);
    lean_dec_ref(v_as_4143_);
    v_r_4150_ = lean_box((v_res_4149_) as usize);
    return v_r_4150_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(
    mut v_as_4151_: *mut LeanObject,
    mut v_i_4152_: usize,
    mut v_stop_4153_: usize,
) -> u8 {
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4155_: u8 = 0;
    let mut v___y_4157_: u8 = 0;
    let mut v___x_4158_: usize = 0;
    let mut v___x_4159_: usize = 0;
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4162_: u8 = 0;
    let mut v_contextDependent_4163_: u8 = 0;
    let mut v___x_4164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4154_ = lean_usize_dec_eq(v_i_4152_, v_stop_4153_);
                if v___x_4154_ == 0 {
                    v___x_4155_ = 1;
                    v___x_4161_ = lean_array_uget_borrowed(v_as_4151_, v_i_4152_);
                    if lean_obj_tag(v___x_4161_) == 0 {
                        v_contextDependent_4162_ = lean_ctor_get_uint8(v___x_4161_, 1 as u32);
                        v___y_4157_ = v_contextDependent_4162_;
                        state = 1;
                        continue;
                    } else {
                        v_contextDependent_4163_ = lean_ctor_get_uint8(
                            v___x_4161_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v___y_4157_ = v_contextDependent_4163_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4164_ = 0;
                    return v___x_4164_;
                }
            }
            1 => {
                if v___y_4157_ == 0 {
                    v___x_4158_ = 1usize;
                    v___x_4159_ = lean_usize_add(v_i_4152_, v___x_4158_);
                    v_i_4152_ = v___x_4159_;
                    state = 0;
                    continue;
                } else {
                    return v___x_4155_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2___boxed(
    mut v_as_4165_: *mut LeanObject,
    mut v_i_4166_: *mut LeanObject,
    mut v_stop_4167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4168_: usize = 0;
    let mut v_stop_boxed_4169_: usize = 0;
    let mut v_res_4170_: u8 = 0;
    let mut v_r_4171_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4168_ = lean_unbox_usize(v_i_4166_);
    lean_dec(v_i_4166_);
    v_stop_boxed_4169_ = lean_unbox_usize(v_stop_4167_);
    lean_dec(v_stop_4167_);
    v_res_4170_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_as_4165_, v_i_boxed_4168_, v_stop_boxed_4169_);
    lean_dec_ref(v_as_4165_);
    v_r_4171_ = lean_box((v_res_4170_) as usize);
    return v_r_4171_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    v___x_4173_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_4174_ = lean_unsigned_to_nat(13);
    v___x_4175_ = lean_unsigned_to_nat(401);
    v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0;
    v___x_4177_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_4178_ = l_mkPanicMessageWithDecl(
        v___x_4177_,
        v___x_4176_,
        v___x_4175_,
        v___x_4174_,
        v___x_4173_,
    );
    return v___x_4178_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(
    mut v_argResults_4179_: *mut LeanObject,
    mut v_as_4180_: *mut LeanObject,
    mut v_sz_4181_: usize,
    mut v_i_4182_: usize,
    mut v_b_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: usize = 0;
    let mut v___x_4197_: usize = 0;
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v_snd_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v_fst_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v_fst_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v_fst_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v_array_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v_a_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instNew_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: u8 = 0;
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4308_: u8 = 0;
    let mut v_a_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: u8 = 0;
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4322_: u8 = 0;
    let mut v_a_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4330_: u8 = 0;
    let mut v_a_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_a_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4362_: u8 = 0;
    let mut v_e_x27_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4382_: u8 = 0;
    let mut v_reuseFailAlloc_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_unused_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut v_unused_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut v_unused_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut v_unused_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4394_: u8 = 0;
    let mut v_unused_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4396_: u8 = 0;
    let mut v_unused_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4199_ = lean_usize_dec_lt(v_i_4182_, v_sz_4181_);
                if v___x_4199_ == 0 {
                    v___x_4200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4200_, 0, v_b_4183_);
                    return v___x_4200_;
                } else {
                    v_snd_4201_ = lean_ctor_get(v_b_4183_, 1);
                    v_isSharedCheck_4396_ = (!lean_is_exclusive(v_b_4183_)) as u8;
                    if v_isSharedCheck_4396_ == 0 {
                        v_unused_4397_ = lean_ctor_get(v_b_4183_, 0);
                        lean_dec(v_unused_4397_);
                        v___x_4203_ = v_b_4183_;
                        v_isShared_4204_ = v_isSharedCheck_4396_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4201_);
                        lean_dec(v_b_4183_);
                        v___x_4203_ = lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4396_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4196_ = 1usize;
                v___x_4197_ = lean_usize_add(v_i_4182_, v___x_4196_);
                v_i_4182_ = v___x_4197_;
                v_b_4183_ = v_a_4195_;
                state = 0;
                continue;
            }
            2 => {
                v_snd_4205_ = lean_ctor_get(v_snd_4201_, 1);
                lean_inc(v_snd_4205_);
                v_snd_4206_ = lean_ctor_get(v_snd_4205_, 1);
                lean_inc(v_snd_4206_);
                v_snd_4207_ = lean_ctor_get(v_snd_4206_, 1);
                lean_inc(v_snd_4207_);
                v_snd_4208_ = lean_ctor_get(v_snd_4207_, 1);
                lean_inc(v_snd_4208_);
                v_fst_4209_ = lean_ctor_get(v_snd_4201_, 0);
                v_isSharedCheck_4394_ = (!lean_is_exclusive(v_snd_4201_)) as u8;
                if v_isSharedCheck_4394_ == 0 {
                    v_unused_4395_ = lean_ctor_get(v_snd_4201_, 1);
                    lean_dec(v_unused_4395_);
                    v___x_4211_ = v_snd_4201_;
                    v_isShared_4212_ = v_isSharedCheck_4394_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_4209_);
                    lean_dec(v_snd_4201_);
                    v___x_4211_ = lean_box(0);
                    v_isShared_4212_ = v_isSharedCheck_4394_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4213_ = lean_ctor_get(v_snd_4205_, 0);
                v_isSharedCheck_4392_ = (!lean_is_exclusive(v_snd_4205_)) as u8;
                if v_isSharedCheck_4392_ == 0 {
                    v_unused_4393_ = lean_ctor_get(v_snd_4205_, 1);
                    lean_dec(v_unused_4393_);
                    v___x_4215_ = v_snd_4205_;
                    v_isShared_4216_ = v_isSharedCheck_4392_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_fst_4213_);
                    lean_dec(v_snd_4205_);
                    v___x_4215_ = lean_box(0);
                    v_isShared_4216_ = v_isSharedCheck_4392_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_fst_4217_ = lean_ctor_get(v_snd_4206_, 0);
                v_isSharedCheck_4390_ = (!lean_is_exclusive(v_snd_4206_)) as u8;
                if v_isSharedCheck_4390_ == 0 {
                    v_unused_4391_ = lean_ctor_get(v_snd_4206_, 1);
                    lean_dec(v_unused_4391_);
                    v___x_4219_ = v_snd_4206_;
                    v_isShared_4220_ = v_isSharedCheck_4390_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_fst_4217_);
                    lean_dec(v_snd_4206_);
                    v___x_4219_ = lean_box(0);
                    v_isShared_4220_ = v_isSharedCheck_4390_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_4221_ = lean_ctor_get(v_snd_4207_, 0);
                v_isSharedCheck_4388_ = (!lean_is_exclusive(v_snd_4207_)) as u8;
                if v_isSharedCheck_4388_ == 0 {
                    v_unused_4389_ = lean_ctor_get(v_snd_4207_, 1);
                    lean_dec(v_unused_4389_);
                    v___x_4223_ = v_snd_4207_;
                    v_isShared_4224_ = v_isSharedCheck_4388_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_fst_4221_);
                    lean_dec(v_snd_4207_);
                    v___x_4223_ = lean_box(0);
                    v_isShared_4224_ = v_isSharedCheck_4388_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_array_4225_ = lean_ctor_get(v_snd_4208_, 0);
                v_start_4226_ = lean_ctor_get(v_snd_4208_, 1);
                v_stop_4227_ = lean_ctor_get(v_snd_4208_, 2);
                v___x_4228_ = lean_box(0);
                v___x_4229_ = lean_nat_dec_lt(v_start_4226_, v_stop_4227_);
                if v___x_4229_ == 0 {
                    if v_isShared_4224_ == 0 {
                        v___x_4231_ = v___x_4223_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_fst_4221_);
                        lean_ctor_set(v_reuseFailAlloc_4245_, 1, v_snd_4208_);
                        v___x_4231_ = v_reuseFailAlloc_4245_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_4227_);
                    lean_inc(v_start_4226_);
                    lean_inc_ref(v_array_4225_);
                    v_isSharedCheck_4384_ = (!lean_is_exclusive(v_snd_4208_)) as u8;
                    if v_isSharedCheck_4384_ == 0 {
                        v_unused_4385_ = lean_ctor_get(v_snd_4208_, 2);
                        lean_dec(v_unused_4385_);
                        v_unused_4386_ = lean_ctor_get(v_snd_4208_, 1);
                        lean_dec(v_unused_4386_);
                        v_unused_4387_ = lean_ctor_get(v_snd_4208_, 0);
                        lean_dec(v_unused_4387_);
                        v___x_4247_ = v_snd_4208_;
                        v_isShared_4248_ = v_isSharedCheck_4384_;
                        state = 12;
                        continue;
                    } else {
                        lean_dec(v_snd_4208_);
                        v___x_4247_ = lean_box(0);
                        v_isShared_4248_ = v_isSharedCheck_4384_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4220_ == 0 {
                    lean_ctor_set(v___x_4219_, 1, v___x_4231_);
                    v___x_4233_ = v___x_4219_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_fst_4217_);
                    lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4231_);
                    v___x_4233_ = v_reuseFailAlloc_4244_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4216_ == 0 {
                    lean_ctor_set(v___x_4215_, 1, v___x_4233_);
                    v___x_4235_ = v___x_4215_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_fst_4213_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 1, v___x_4233_);
                    v___x_4235_ = v_reuseFailAlloc_4243_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4212_ == 0 {
                    lean_ctor_set(v___x_4211_, 1, v___x_4235_);
                    v___x_4237_ = v___x_4211_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_fst_4209_);
                    lean_ctor_set(v_reuseFailAlloc_4242_, 1, v___x_4235_);
                    v___x_4237_ = v_reuseFailAlloc_4242_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4204_ == 0 {
                    lean_ctor_set(v___x_4203_, 1, v___x_4237_);
                    lean_ctor_set(v___x_4203_, 0, v___x_4228_);
                    v___x_4239_ = v___x_4203_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4228_);
                    lean_ctor_set(v_reuseFailAlloc_4241_, 1, v___x_4237_);
                    v___x_4239_ = v_reuseFailAlloc_4241_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4240_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4240_, 0, v___x_4239_);
                return v___x_4240_;
            }
            12 => {
                v_a_4249_ = lean_array_uget_borrowed(v_as_4180_, v_i_4182_);
                v___x_4250_ = lean_array_fget(v_array_4225_, v_start_4226_);
                v___x_4251_ = lean_unsigned_to_nat(1);
                v___x_4252_ = lean_nat_add(v_start_4226_, v___x_4251_);
                lean_dec(v_start_4226_);
                if v_isShared_4248_ == 0 {
                    lean_ctor_set(v___x_4247_, 1, v___x_4252_);
                    v___x_4254_ = v___x_4247_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_array_4225_);
                    lean_ctor_set(v_reuseFailAlloc_4383_, 1, v___x_4252_);
                    lean_ctor_set(v_reuseFailAlloc_4383_, 2, v_stop_4227_);
                    v___x_4254_ = v_reuseFailAlloc_4383_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                lean_inc(v_a_4249_);
                v___x_4255_ = l_Lean_Expr_app___override(v_fst_4209_, v_a_4249_);
                v___x_4256_ = l_Lean_Expr_bindingBody_x21(v_fst_4213_);
                lean_dec(v_fst_4213_);
                v___x_4285_ = (lean_unbox(v___x_4250_) as u8);
                lean_dec(v___x_4250_);
                match v___x_4285_ {
                    0 => {
                        lean_del_object(v___x_4223_);
                        lean_del_object(v___x_4219_);
                        lean_del_object(v___x_4215_);
                        lean_del_object(v___x_4211_);
                        lean_del_object(v___x_4203_);
                        state = 20;
                        continue;
                    }
                    3 => {
                        lean_del_object(v___x_4223_);
                        lean_del_object(v___x_4219_);
                        lean_del_object(v___x_4215_);
                        lean_del_object(v___x_4211_);
                        lean_del_object(v___x_4203_);
                        state = 20;
                        continue;
                    }
                    5 => {
                        lean_del_object(v___x_4223_);
                        lean_del_object(v___x_4219_);
                        lean_del_object(v___x_4215_);
                        lean_del_object(v___x_4211_);
                        lean_del_object(v___x_4203_);
                        lean_inc_n(v_a_4249_, 2);
                        v___x_4286_ = lean_array_push(v_fst_4221_, v_a_4249_);
                        v___x_4297_ = l_Lean_Meta_Sym_inferType___redArg(
                            v_a_4249_,
                            v___y_4188_,
                            v___y_4189_,
                            v___y_4190_,
                            v___y_4191_,
                            v___y_4192_,
                        );
                        if lean_obj_tag(v___x_4297_) == 0 {
                            v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
                            lean_inc(v_a_4298_);
                            lean_dec_ref_known(v___x_4297_, 1);
                            v___x_4299_ = l_Lean_Expr_bindingDomain_x21(v___x_4256_);
                            v___x_4300_ = lean_expr_instantiate_rev(v___x_4299_, v___x_4286_);
                            lean_dec_ref(v___x_4299_);
                            lean_inc_ref(v___x_4300_);
                            v___x_4301_ = l_Lean_Meta_Sym_isDefEqI___redArg(
                                v_a_4298_,
                                v___x_4300_,
                                v___y_4188_,
                                v___y_4189_,
                                v___y_4190_,
                                v___y_4191_,
                                v___y_4192_,
                            );
                            if lean_obj_tag(v___x_4301_) == 0 {
                                v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
                                lean_inc(v_a_4302_);
                                lean_dec_ref_known(v___x_4301_, 1);
                                v___x_4303_ = (lean_unbox(v_a_4302_) as u8);
                                if v___x_4303_ == 0 {
                                    v___x_4304_ = l_Lean_Meta_trySynthInstance(
                                        v___x_4300_,
                                        v___x_4228_,
                                        v___y_4189_,
                                        v___y_4190_,
                                        v___y_4191_,
                                        v___y_4192_,
                                    );
                                    if lean_obj_tag(v___x_4304_) == 0 {
                                        v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
                                        v_isSharedCheck_4322_ =
                                            (!lean_is_exclusive(v___x_4304_)) as u8;
                                        if v_isSharedCheck_4322_ == 0 {
                                            v___x_4307_ = v___x_4304_;
                                            v_isShared_4308_ = v_isSharedCheck_4322_;
                                            state = 22;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4305_);
                                            lean_dec(v___x_4304_);
                                            v___x_4307_ = lean_box(0);
                                            v_isShared_4308_ = v_isSharedCheck_4322_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_4302_);
                                        lean_dec_ref(v___x_4286_);
                                        lean_dec_ref(v___x_4256_);
                                        lean_dec_ref(v___x_4255_);
                                        lean_dec_ref(v___x_4254_);
                                        lean_dec(v_fst_4217_);
                                        v_a_4323_ = lean_ctor_get(v___x_4304_, 0);
                                        v_isSharedCheck_4330_ =
                                            (!lean_is_exclusive(v___x_4304_)) as u8;
                                        if v_isSharedCheck_4330_ == 0 {
                                            v___x_4325_ = v___x_4304_;
                                            v_isShared_4326_ = v_isSharedCheck_4330_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4323_);
                                            lean_dec(v___x_4304_);
                                            v___x_4325_ = lean_box(0);
                                            v_isShared_4326_ = v_isSharedCheck_4330_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_4302_);
                                    lean_dec_ref(v___x_4300_);
                                    lean_inc(v_a_4249_);
                                    v_instNew_4288_ = v_a_4249_;
                                    state = 21;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_4300_);
                                lean_dec_ref(v___x_4286_);
                                lean_dec_ref(v___x_4256_);
                                lean_dec_ref(v___x_4255_);
                                lean_dec_ref(v___x_4254_);
                                lean_dec(v_fst_4217_);
                                v_a_4331_ = lean_ctor_get(v___x_4301_, 0);
                                v_isSharedCheck_4338_ = (!lean_is_exclusive(v___x_4301_)) as u8;
                                if v_isSharedCheck_4338_ == 0 {
                                    v___x_4333_ = v___x_4301_;
                                    v_isShared_4334_ = v_isSharedCheck_4338_;
                                    state = 26;
                                    continue;
                                } else {
                                    lean_inc(v_a_4331_);
                                    lean_dec(v___x_4301_);
                                    v___x_4333_ = lean_box(0);
                                    v_isShared_4334_ = v_isSharedCheck_4338_;
                                    state = 26;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_4286_);
                            lean_dec_ref(v___x_4256_);
                            lean_dec_ref(v___x_4255_);
                            lean_dec_ref(v___x_4254_);
                            lean_dec(v_fst_4217_);
                            v_a_4339_ = lean_ctor_get(v___x_4297_, 0);
                            v_isSharedCheck_4346_ = (!lean_is_exclusive(v___x_4297_)) as u8;
                            if v_isSharedCheck_4346_ == 0 {
                                v___x_4341_ = v___x_4297_;
                                v_isShared_4342_ = v_isSharedCheck_4346_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_4339_);
                                lean_dec(v___x_4297_);
                                v___x_4341_ = lean_box(0);
                                v_isShared_4342_ = v_isSharedCheck_4346_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                    2 => {
                        v___x_4347_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default;
                        lean_inc(v_a_4249_);
                        v___x_4348_ = lean_array_push(v_fst_4221_, v_a_4249_);
                        v___x_4349_ =
                            lean_array_get_borrowed(v___x_4347_, v_argResults_4179_, v_fst_4217_);
                        if lean_obj_tag(v___x_4349_) == 0 {
                            lean_inc(v_a_4249_);
                            v___x_4350_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
                                v_a_4249_,
                                v___y_4188_,
                                v___y_4189_,
                                v___y_4190_,
                                v___y_4191_,
                                v___y_4192_,
                            );
                            if lean_obj_tag(v___x_4350_) == 0 {
                                v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
                                lean_inc_n(v_a_4351_, 2);
                                lean_dec_ref_known(v___x_4350_, 1);
                                lean_inc_n(v_a_4249_, 2);
                                v___x_4352_ = l_Lean_mkAppB(v___x_4255_, v_a_4249_, v_a_4351_);
                                v___x_4353_ = lean_array_push(v___x_4348_, v_a_4249_);
                                v___x_4354_ = lean_array_push(v___x_4353_, v_a_4351_);
                                v_proof_4258_ = v___x_4352_;
                                v_subst_4259_ = v___x_4354_;
                                state = 14;
                                continue;
                            } else {
                                lean_dec_ref(v___x_4348_);
                                lean_dec_ref(v___x_4256_);
                                lean_dec_ref(v___x_4255_);
                                lean_dec_ref(v___x_4254_);
                                lean_del_object(v___x_4223_);
                                lean_del_object(v___x_4219_);
                                lean_dec(v_fst_4217_);
                                lean_del_object(v___x_4215_);
                                lean_del_object(v___x_4211_);
                                lean_del_object(v___x_4203_);
                                v_a_4355_ = lean_ctor_get(v___x_4350_, 0);
                                v_isSharedCheck_4362_ = (!lean_is_exclusive(v___x_4350_)) as u8;
                                if v_isSharedCheck_4362_ == 0 {
                                    v___x_4357_ = v___x_4350_;
                                    v_isShared_4358_ = v_isSharedCheck_4362_;
                                    state = 30;
                                    continue;
                                } else {
                                    lean_inc(v_a_4355_);
                                    lean_dec(v___x_4350_);
                                    v___x_4357_ = lean_box(0);
                                    v_isShared_4358_ = v_isSharedCheck_4362_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            v_e_x27_4363_ = lean_ctor_get(v___x_4349_, 0);
                            v_proof_4364_ = lean_ctor_get(v___x_4349_, 1);
                            lean_inc_ref_n(v_proof_4364_, 2);
                            lean_inc_ref_n(v_e_x27_4363_, 2);
                            v___x_4365_ = l_Lean_mkAppB(v___x_4255_, v_e_x27_4363_, v_proof_4364_);
                            v___x_4366_ = lean_array_push(v___x_4348_, v_e_x27_4363_);
                            v___x_4367_ = lean_array_push(v___x_4366_, v_proof_4364_);
                            v_proof_4258_ = v___x_4365_;
                            v_subst_4259_ = v___x_4367_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        lean_del_object(v___x_4223_);
                        lean_del_object(v___x_4219_);
                        lean_del_object(v___x_4215_);
                        lean_del_object(v___x_4211_);
                        lean_del_object(v___x_4203_);
                        v___x_4368_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__1);
                        v___x_4369_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__0(v___x_4368_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
                        if lean_obj_tag(v___x_4369_) == 0 {
                            lean_dec_ref_known(v___x_4369_, 1);
                            v___x_4370_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4370_, 0, v_fst_4221_);
                            lean_ctor_set(v___x_4370_, 1, v___x_4254_);
                            v___x_4371_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4371_, 0, v_fst_4217_);
                            lean_ctor_set(v___x_4371_, 1, v___x_4370_);
                            v___x_4372_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4372_, 0, v___x_4256_);
                            lean_ctor_set(v___x_4372_, 1, v___x_4371_);
                            v___x_4373_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4373_, 0, v___x_4255_);
                            lean_ctor_set(v___x_4373_, 1, v___x_4372_);
                            v___x_4374_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4374_, 0, v___x_4228_);
                            lean_ctor_set(v___x_4374_, 1, v___x_4373_);
                            v_a_4195_ = v___x_4374_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___x_4256_);
                            lean_dec_ref(v___x_4255_);
                            lean_dec_ref(v___x_4254_);
                            lean_dec(v_fst_4221_);
                            lean_dec(v_fst_4217_);
                            v_a_4375_ = lean_ctor_get(v___x_4369_, 0);
                            v_isSharedCheck_4382_ = (!lean_is_exclusive(v___x_4369_)) as u8;
                            if v_isSharedCheck_4382_ == 0 {
                                v___x_4377_ = v___x_4369_;
                                v_isShared_4378_ = v_isSharedCheck_4382_;
                                state = 32;
                                continue;
                            } else {
                                lean_inc(v_a_4375_);
                                lean_dec(v___x_4369_);
                                v___x_4377_ = lean_box(0);
                                v_isShared_4378_ = v_isSharedCheck_4382_;
                                state = 32;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                v___x_4260_ = l_Lean_Expr_bindingBody_x21(v___x_4256_);
                lean_dec_ref(v___x_4256_);
                v___x_4261_ = l_Lean_Expr_bindingBody_x21(v___x_4260_);
                lean_dec_ref(v___x_4260_);
                v___x_4262_ = lean_nat_add(v_fst_4217_, v___x_4251_);
                lean_dec(v_fst_4217_);
                if v_isShared_4224_ == 0 {
                    lean_ctor_set(v___x_4223_, 1, v___x_4254_);
                    lean_ctor_set(v___x_4223_, 0, v_subst_4259_);
                    v___x_4264_ = v___x_4223_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_subst_4259_);
                    lean_ctor_set(v_reuseFailAlloc_4277_, 1, v___x_4254_);
                    v___x_4264_ = v_reuseFailAlloc_4277_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4220_ == 0 {
                    lean_ctor_set(v___x_4219_, 1, v___x_4264_);
                    lean_ctor_set(v___x_4219_, 0, v___x_4262_);
                    v___x_4266_ = v___x_4219_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4262_);
                    lean_ctor_set(v_reuseFailAlloc_4276_, 1, v___x_4264_);
                    v___x_4266_ = v_reuseFailAlloc_4276_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4216_ == 0 {
                    lean_ctor_set(v___x_4215_, 1, v___x_4266_);
                    lean_ctor_set(v___x_4215_, 0, v___x_4261_);
                    v___x_4268_ = v___x_4215_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4261_);
                    lean_ctor_set(v_reuseFailAlloc_4275_, 1, v___x_4266_);
                    v___x_4268_ = v_reuseFailAlloc_4275_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4212_ == 0 {
                    lean_ctor_set(v___x_4211_, 1, v___x_4268_);
                    lean_ctor_set(v___x_4211_, 0, v_proof_4258_);
                    v___x_4270_ = v___x_4211_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_proof_4258_);
                    lean_ctor_set(v_reuseFailAlloc_4274_, 1, v___x_4268_);
                    v___x_4270_ = v_reuseFailAlloc_4274_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_4204_ == 0 {
                    lean_ctor_set(v___x_4203_, 1, v___x_4270_);
                    lean_ctor_set(v___x_4203_, 0, v___x_4228_);
                    v___x_4272_ = v___x_4203_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4228_);
                    lean_ctor_set(v_reuseFailAlloc_4273_, 1, v___x_4270_);
                    v___x_4272_ = v_reuseFailAlloc_4273_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v_a_4195_ = v___x_4272_;
                state = 1;
                continue;
            }
            20 => {
                lean_inc(v_a_4249_);
                v___x_4279_ = lean_array_push(v_fst_4221_, v_a_4249_);
                v___x_4280_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4280_, 0, v___x_4279_);
                lean_ctor_set(v___x_4280_, 1, v___x_4254_);
                v___x_4281_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4281_, 0, v_fst_4217_);
                lean_ctor_set(v___x_4281_, 1, v___x_4280_);
                v___x_4282_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4282_, 0, v___x_4256_);
                lean_ctor_set(v___x_4282_, 1, v___x_4281_);
                v___x_4283_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4283_, 0, v___x_4255_);
                lean_ctor_set(v___x_4283_, 1, v___x_4282_);
                v___x_4284_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4284_, 0, v___x_4228_);
                lean_ctor_set(v___x_4284_, 1, v___x_4283_);
                v_a_4195_ = v___x_4284_;
                state = 1;
                continue;
            }
            21 => {
                lean_inc_ref(v_instNew_4288_);
                v___x_4289_ = l_Lean_Expr_app___override(v___x_4255_, v_instNew_4288_);
                v___x_4290_ = lean_array_push(v___x_4286_, v_instNew_4288_);
                v___x_4291_ = l_Lean_Expr_bindingBody_x21(v___x_4256_);
                lean_dec_ref(v___x_4256_);
                v___x_4292_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4292_, 0, v___x_4290_);
                lean_ctor_set(v___x_4292_, 1, v___x_4254_);
                v___x_4293_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4293_, 0, v_fst_4217_);
                lean_ctor_set(v___x_4293_, 1, v___x_4292_);
                v___x_4294_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4294_, 0, v___x_4291_);
                lean_ctor_set(v___x_4294_, 1, v___x_4293_);
                v___x_4295_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4295_, 0, v___x_4289_);
                lean_ctor_set(v___x_4295_, 1, v___x_4294_);
                v___x_4296_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4296_, 0, v___x_4228_);
                lean_ctor_set(v___x_4296_, 1, v___x_4295_);
                v_a_4195_ = v___x_4296_;
                state = 1;
                continue;
            }
            22 => {
                if lean_obj_tag(v_a_4305_) == 1 {
                    lean_del_object(v___x_4307_);
                    lean_dec(v_a_4302_);
                    v_a_4309_ = lean_ctor_get(v_a_4305_, 0);
                    lean_inc(v_a_4309_);
                    lean_dec_ref_known(v_a_4305_, 1);
                    v_instNew_4288_ = v_a_4309_;
                    state = 21;
                    continue;
                } else {
                    lean_dec(v_a_4305_);
                    v___x_4310_ = lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_4311_ = (lean_unbox(v_a_4302_) as u8);
                    lean_ctor_set_uint8(v___x_4310_, 0 as u32, v___x_4311_);
                    v___x_4312_ = (lean_unbox(v_a_4302_) as u8);
                    lean_dec(v_a_4302_);
                    lean_ctor_set_uint8(v___x_4310_, 1 as u32, v___x_4312_);
                    v___x_4313_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4313_, 0, v___x_4310_);
                    v___x_4314_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4314_, 0, v___x_4286_);
                    lean_ctor_set(v___x_4314_, 1, v___x_4254_);
                    v___x_4315_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4315_, 0, v_fst_4217_);
                    lean_ctor_set(v___x_4315_, 1, v___x_4314_);
                    v___x_4316_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4316_, 0, v___x_4256_);
                    lean_ctor_set(v___x_4316_, 1, v___x_4315_);
                    v___x_4317_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4317_, 0, v___x_4255_);
                    lean_ctor_set(v___x_4317_, 1, v___x_4316_);
                    v___x_4318_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4318_, 0, v___x_4313_);
                    lean_ctor_set(v___x_4318_, 1, v___x_4317_);
                    if v_isShared_4308_ == 0 {
                        lean_ctor_set(v___x_4307_, 0, v___x_4318_);
                        v___x_4320_ = v___x_4307_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4318_);
                        v___x_4320_ = v_reuseFailAlloc_4321_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                return v___x_4320_;
            }
            24 => {
                if v_isShared_4326_ == 0 {
                    v___x_4328_ = v___x_4325_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
                    v___x_4328_ = v_reuseFailAlloc_4329_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4328_;
            }
            26 => {
                if v_isShared_4334_ == 0 {
                    v___x_4336_ = v___x_4333_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4336_;
            }
            28 => {
                if v_isShared_4342_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
                    v___x_4344_ = v_reuseFailAlloc_4345_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4344_;
            }
            30 => {
                if v_isShared_4358_ == 0 {
                    v___x_4360_ = v___x_4357_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
                    v___x_4360_ = v_reuseFailAlloc_4361_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4360_;
            }
            32 => {
                if v_isShared_4378_ == 0 {
                    v___x_4380_ = v___x_4377_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___boxed(
    mut v_argResults_4398_: *mut LeanObject,
    mut v_as_4399_: *mut LeanObject,
    mut v_sz_4400_: *mut LeanObject,
    mut v_i_4401_: *mut LeanObject,
    mut v_b_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
    mut v___y_4412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4413_: usize = 0;
    let mut v_i_boxed_4414_: usize = 0;
    let mut v_res_4415_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4413_ = lean_unbox_usize(v_sz_4400_);
    lean_dec(v_sz_4400_);
    v_i_boxed_4414_ = lean_unbox_usize(v_i_4401_);
    lean_dec(v_i_4401_);
    v_res_4415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_4398_, v_as_4399_, v_sz_boxed_4413_, v_i_boxed_4414_, v_b_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
    lean_dec(v___y_4411_);
    lean_dec_ref(v___y_4410_);
    lean_dec(v___y_4409_);
    lean_dec_ref(v___y_4408_);
    lean_dec(v___y_4407_);
    lean_dec_ref(v___y_4406_);
    lean_dec(v___y_4405_);
    lean_dec_ref(v___y_4404_);
    lean_dec(v___y_4403_);
    lean_dec_ref(v_as_4399_);
    lean_dec_ref(v_argResults_4398_);
    return v_res_4415_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    v___x_4416_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_4417_ = lean_unsigned_to_nat(34);
    v___x_4418_ = lean_unsigned_to_nat(402);
    v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1___closed__0;
    v___x_4420_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_4421_ = l_mkPanicMessageWithDecl(
        v___x_4420_,
        v___x_4419_,
        v___x_4418_,
        v___x_4417_,
        v___x_4416_,
    );
    return v___x_4421_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4425_: *mut LeanObject = core::ptr::null_mut();
    v___x_4424_ = lean_box(0);
    v_dummy_4425_ = l_Lean_Expr_sort___override(v___x_4424_);
    return v_dummy_4425_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(
    mut v_e_4429_: *mut LeanObject,
    mut v_argKinds_4430_: *mut LeanObject,
    mut v_type_4431_: *mut LeanObject,
    mut v_proof_4432_: *mut LeanObject,
    mut v_argResults_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4472_: usize = 0;
    let mut v___x_4473_: usize = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4478_: u8 = 0;
    let mut v_fst_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4485_: u8 = 0;
    let mut v___x_4486_: u8 = 0;
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: u8 = 0;
    let mut v___x_4498_: usize = 0;
    let mut v___x_4499_: u8 = 0;
    let mut v_a_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4503_: u8 = 0;
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4507_: u8 = 0;
    let mut v_fst_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: u8 = 0;
    let mut v_arg_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: u8 = 0;
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v_snd_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: usize = 0;
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4531_: u8 = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut v_val_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_a_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4544_: u8 = 0;
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_j_4456_ = lean_unsigned_to_nat(0);
                v_subst_4457_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__1;
                v_dummy_4458_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__2);
                v_nargs_4459_ = l_Lean_Expr_getAppNumArgs(v_e_4429_);
                lean_inc(v_nargs_4459_);
                v___x_4460_ = lean_mk_array(v_nargs_4459_, v_dummy_4458_);
                v___x_4461_ = lean_unsigned_to_nat(1);
                v___x_4462_ = lean_nat_sub(v_nargs_4459_, v___x_4461_);
                lean_dec(v_nargs_4459_);
                v_args_4463_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_4429_,
                    v___x_4460_,
                    v___x_4462_,
                );
                v___x_4464_ = lean_array_get_size(v_argKinds_4430_);
                lean_inc_ref(v_argKinds_4430_);
                v___x_4465_ = l_Array_toSubarray___redArg(v_argKinds_4430_, v_j_4456_, v___x_4464_);
                v___x_4466_ = lean_box(0);
                v___x_4467_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4467_, 0, v_subst_4457_);
                lean_ctor_set(v___x_4467_, 1, v___x_4465_);
                v___x_4468_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4468_, 0, v_j_4456_);
                lean_ctor_set(v___x_4468_, 1, v___x_4467_);
                v___x_4469_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4469_, 0, v_type_4431_);
                lean_ctor_set(v___x_4469_, 1, v___x_4468_);
                v___x_4470_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4470_, 0, v_proof_4432_);
                lean_ctor_set(v___x_4470_, 1, v___x_4469_);
                v___x_4471_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4471_, 0, v___x_4466_);
                lean_ctor_set(v___x_4471_, 1, v___x_4470_);
                v_sz_4472_ = lean_array_size(v_args_4463_);
                v___x_4473_ = 0usize;
                v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__1(v_argResults_4433_, v_args_4463_, v_sz_4472_, v___x_4473_, v___x_4471_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
                lean_dec_ref(v_args_4463_);
                if lean_obj_tag(v___x_4474_) == 0 {
                    v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
                    v_isSharedCheck_4540_ = (!lean_is_exclusive(v___x_4474_)) as u8;
                    if v_isSharedCheck_4540_ == 0 {
                        v___x_4477_ = v___x_4474_;
                        v_isShared_4478_ = v_isSharedCheck_4540_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4475_);
                        lean_dec(v___x_4474_);
                        v___x_4477_ = lean_box(0);
                        v_isShared_4478_ = v_isSharedCheck_4540_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_argKinds_4430_);
                    v_a_4541_ = lean_ctor_get(v___x_4474_, 0);
                    v_isSharedCheck_4548_ = (!lean_is_exclusive(v___x_4474_)) as u8;
                    if v_isSharedCheck_4548_ == 0 {
                        v___x_4543_ = v___x_4474_;
                        v_isShared_4544_ = v_isSharedCheck_4548_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4541_);
                        lean_dec(v___x_4474_);
                        v___x_4543_ = lean_box(0);
                        v_isShared_4544_ = v_isSharedCheck_4548_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4454_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__0);
                v___x_4455_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_4454_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
                return v___x_4455_;
            }
            2 => {
                v_fst_4479_ = lean_ctor_get(v_a_4475_, 0);
                if lean_obj_tag(v_fst_4479_) == 0 {
                    v_snd_4480_ = lean_ctor_get(v_a_4475_, 1);
                    lean_inc(v_snd_4480_);
                    lean_dec(v_a_4475_);
                    v_fst_4481_ = lean_ctor_get(v_snd_4480_, 0);
                    lean_inc(v_fst_4481_);
                    v_snd_4482_ = lean_ctor_get(v_snd_4480_, 1);
                    lean_inc(v_snd_4482_);
                    lean_dec(v_snd_4480_);
                    v_fst_4508_ = lean_ctor_get(v_snd_4482_, 0);
                    lean_inc(v_fst_4508_);
                    v_snd_4509_ = lean_ctor_get(v_snd_4482_, 1);
                    lean_inc(v_snd_4509_);
                    lean_dec(v_snd_4482_);
                    v___x_4510_ = l_Lean_Expr_cleanupAnnotations(v_fst_4508_);
                    v___x_4511_ = l_Lean_Expr_isApp(v___x_4510_);
                    if v___x_4511_ == 0 {
                        lean_dec_ref(v___x_4510_);
                        lean_dec(v_snd_4509_);
                        lean_dec(v_fst_4481_);
                        lean_del_object(v___x_4477_);
                        lean_dec_ref(v_argKinds_4430_);
                        v___y_4445_ = v___y_4434_;
                        v___y_4446_ = v___y_4435_;
                        v___y_4447_ = v___y_4436_;
                        v___y_4448_ = v___y_4437_;
                        v___y_4449_ = v___y_4438_;
                        v___y_4450_ = v___y_4439_;
                        v___y_4451_ = v___y_4440_;
                        v___y_4452_ = v___y_4441_;
                        v___y_4453_ = v___y_4442_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_4512_ = lean_ctor_get(v___x_4510_, 1);
                        lean_inc_ref(v_arg_4512_);
                        v___x_4513_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4510_);
                        v___x_4514_ = l_Lean_Expr_isApp(v___x_4513_);
                        if v___x_4514_ == 0 {
                            lean_dec_ref(v___x_4513_);
                            lean_dec_ref(v_arg_4512_);
                            lean_dec(v_snd_4509_);
                            lean_dec(v_fst_4481_);
                            lean_del_object(v___x_4477_);
                            lean_dec_ref(v_argKinds_4430_);
                            v___y_4445_ = v___y_4434_;
                            v___y_4446_ = v___y_4435_;
                            v___y_4447_ = v___y_4436_;
                            v___y_4448_ = v___y_4437_;
                            v___y_4449_ = v___y_4438_;
                            v___y_4450_ = v___y_4439_;
                            v___y_4451_ = v___y_4440_;
                            v___y_4452_ = v___y_4441_;
                            v___y_4453_ = v___y_4442_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4515_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4513_);
                            v___x_4516_ = l_Lean_Expr_isApp(v___x_4515_);
                            if v___x_4516_ == 0 {
                                lean_dec_ref(v___x_4515_);
                                lean_dec_ref(v_arg_4512_);
                                lean_dec(v_snd_4509_);
                                lean_dec(v_fst_4481_);
                                lean_del_object(v___x_4477_);
                                lean_dec_ref(v_argKinds_4430_);
                                v___y_4445_ = v___y_4434_;
                                v___y_4446_ = v___y_4435_;
                                v___y_4447_ = v___y_4436_;
                                v___y_4448_ = v___y_4437_;
                                v___y_4449_ = v___y_4438_;
                                v___y_4450_ = v___y_4439_;
                                v___y_4451_ = v___y_4440_;
                                v___y_4452_ = v___y_4441_;
                                v___y_4453_ = v___y_4442_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4515_);
                                v___x_4518_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___closed__4;
                                v___x_4519_ = l_Lean_Expr_isConstOf(v___x_4517_, v___x_4518_);
                                lean_dec_ref(v___x_4517_);
                                if v___x_4519_ == 0 {
                                    lean_dec_ref(v_arg_4512_);
                                    lean_dec(v_snd_4509_);
                                    lean_dec(v_fst_4481_);
                                    lean_del_object(v___x_4477_);
                                    lean_dec_ref(v_argKinds_4430_);
                                    v___y_4445_ = v___y_4434_;
                                    v___y_4446_ = v___y_4435_;
                                    v___y_4447_ = v___y_4436_;
                                    v___y_4448_ = v___y_4437_;
                                    v___y_4449_ = v___y_4438_;
                                    v___y_4450_ = v___y_4439_;
                                    v___y_4451_ = v___y_4440_;
                                    v___y_4452_ = v___y_4441_;
                                    v___y_4453_ = v___y_4442_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_snd_4520_ = lean_ctor_get(v_snd_4509_, 1);
                                    lean_inc(v_snd_4520_);
                                    lean_dec(v_snd_4509_);
                                    v_fst_4521_ = lean_ctor_get(v_snd_4520_, 0);
                                    lean_inc(v_fst_4521_);
                                    lean_dec(v_snd_4520_);
                                    v___x_4522_ =
                                        lean_expr_instantiate_rev(v_arg_4512_, v_fst_4521_);
                                    lean_dec(v_fst_4521_);
                                    lean_dec_ref(v_arg_4512_);
                                    v___x_4523_ = lean_nat_dec_lt(v_j_4456_, v___x_4464_);
                                    if v___x_4523_ == 0 {
                                        lean_dec_ref(v_argKinds_4430_);
                                        v_rhs_4492_ = v___x_4522_;
                                        v___y_4493_ = v___y_4438_;
                                        state = 5;
                                        continue;
                                    } else {
                                        if v___x_4523_ == 0 {
                                            lean_dec_ref(v_argKinds_4430_);
                                            v_rhs_4492_ = v___x_4522_;
                                            v___y_4493_ = v___y_4438_;
                                            state = 5;
                                            continue;
                                        } else {
                                            v___x_4524_ = lean_usize_of_nat(v___x_4464_);
                                            v___x_4525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__3(v___x_4519_, v_argKinds_4430_, v___x_4473_, v___x_4524_);
                                            lean_dec_ref(v_argKinds_4430_);
                                            if v___x_4525_ == 0 {
                                                v_rhs_4492_ = v___x_4522_;
                                                v___y_4493_ = v___y_4438_;
                                                state = 5;
                                                continue;
                                            } else {
                                                v___x_4526_ =
                                                    l_Lean_Meta_Simp_removeUnnecessaryCasts(
                                                        v___x_4522_,
                                                        v___y_4439_,
                                                        v___y_4440_,
                                                        v___y_4441_,
                                                        v___y_4442_,
                                                    );
                                                if lean_obj_tag(v___x_4526_) == 0 {
                                                    v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
                                                    lean_inc(v_a_4527_);
                                                    lean_dec_ref_known(v___x_4526_, 1);
                                                    v_rhs_4492_ = v_a_4527_;
                                                    v___y_4493_ = v___y_4438_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    lean_dec(v_fst_4481_);
                                                    lean_del_object(v___x_4477_);
                                                    v_a_4528_ = lean_ctor_get(v___x_4526_, 0);
                                                    v_isSharedCheck_4535_ =
                                                        (!lean_is_exclusive(v___x_4526_)) as u8;
                                                    if v_isSharedCheck_4535_ == 0 {
                                                        v___x_4530_ = v___x_4526_;
                                                        v_isShared_4531_ = v_isSharedCheck_4535_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_4528_);
                                                        lean_dec(v___x_4526_);
                                                        v___x_4530_ = lean_box(0);
                                                        v_isShared_4531_ = v_isSharedCheck_4535_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_inc_ref(v_fst_4479_);
                    lean_dec(v_a_4475_);
                    lean_dec_ref(v_argKinds_4430_);
                    v_val_4536_ = lean_ctor_get(v_fst_4479_, 0);
                    lean_inc(v_val_4536_);
                    lean_dec_ref_known(v_fst_4479_, 1);
                    if v_isShared_4478_ == 0 {
                        lean_ctor_set(v___x_4477_, 0, v_val_4536_);
                        v___x_4538_ = v___x_4477_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_val_4536_);
                        v___x_4538_ = v_reuseFailAlloc_4539_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4486_ = 0;
                v___x_4487_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_4487_, 0, v___y_4484_);
                lean_ctor_set(v___x_4487_, 1, v_fst_4481_);
                lean_ctor_set_uint8(
                    v___x_4487_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_4486_,
                );
                lean_ctor_set_uint8(
                    v___x_4487_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_4485_,
                );
                if v_isShared_4478_ == 0 {
                    lean_ctor_set(v___x_4477_, 0, v___x_4487_);
                    v___x_4489_ = v___x_4477_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
                    v___x_4489_ = v_reuseFailAlloc_4490_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4489_;
            }
            5 => {
                v___x_4494_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_rhs_4492_, v___y_4493_);
                if lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
                    lean_inc(v_a_4495_);
                    lean_dec_ref_known(v___x_4494_, 1);
                    v___x_4496_ = lean_array_get_size(v_argResults_4433_);
                    v___x_4497_ = lean_nat_dec_lt(v_j_4456_, v___x_4496_);
                    if v___x_4497_ == 0 {
                        v___y_4484_ = v_a_4495_;
                        v___y_4485_ = v___x_4497_;
                        state = 3;
                        continue;
                    } else {
                        if v___x_4497_ == 0 {
                            v___y_4484_ = v_a_4495_;
                            v___y_4485_ = v___x_4497_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4498_ = lean_usize_of_nat(v___x_4496_);
                            v___x_4499_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_spec__2(v_argResults_4433_, v___x_4473_, v___x_4498_);
                            v___y_4484_ = v_a_4495_;
                            v___y_4485_ = v___x_4499_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_4481_);
                    lean_del_object(v___x_4477_);
                    v_a_4500_ = lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4507_ = (!lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4507_ == 0 {
                        v___x_4502_ = v___x_4494_;
                        v_isShared_4503_ = v_isSharedCheck_4507_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4500_);
                        lean_dec(v___x_4494_);
                        v___x_4502_ = lean_box(0);
                        v_isShared_4503_ = v_isSharedCheck_4507_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4503_ == 0 {
                    v___x_4505_ = v___x_4502_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
                    v___x_4505_ = v_reuseFailAlloc_4506_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4505_;
            }
            8 => {
                if v_isShared_4531_ == 0 {
                    v___x_4533_ = v___x_4530_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4528_);
                    v___x_4533_ = v_reuseFailAlloc_4534_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4533_;
            }
            10 => {
                return v___x_4538_;
            }
            11 => {
                if v_isShared_4544_ == 0 {
                    v___x_4546_ = v___x_4543_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
                    v___x_4546_ = v_reuseFailAlloc_4547_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed(
    mut v_e_4549_: *mut LeanObject,
    mut v_argKinds_4550_: *mut LeanObject,
    mut v_type_4551_: *mut LeanObject,
    mut v_proof_4552_: *mut LeanObject,
    mut v_argResults_4553_: *mut LeanObject,
    mut v___y_4554_: *mut LeanObject,
    mut v___y_4555_: *mut LeanObject,
    mut v___y_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
    mut v___y_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4564_: *mut LeanObject = core::ptr::null_mut();
    v_res_4564_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0(
            v_e_4549_,
            v_argKinds_4550_,
            v_type_4551_,
            v_proof_4552_,
            v_argResults_4553_,
            v___y_4554_,
            v___y_4555_,
            v___y_4556_,
            v___y_4557_,
            v___y_4558_,
            v___y_4559_,
            v___y_4560_,
            v___y_4561_,
            v___y_4562_,
        );
    lean_dec(v___y_4562_);
    lean_dec_ref(v___y_4561_);
    lean_dec(v___y_4560_);
    lean_dec_ref(v___y_4559_);
    lean_dec(v___y_4558_);
    lean_dec_ref(v___y_4557_);
    lean_dec(v___y_4556_);
    lean_dec_ref(v___y_4555_);
    lean_dec(v___y_4554_);
    lean_dec_ref(v_argResults_4553_);
    return v_res_4564_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(
    mut v___x_4565_: u8,
    mut v_x_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
    mut v___y_4569_: *mut LeanObject,
    mut v___y_4570_: *mut LeanObject,
    mut v___y_4571_: *mut LeanObject,
    mut v___y_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    v___x_4577_ = lean_alloc_ctor(0, 0, (2) as u32);
    lean_ctor_set_uint8(v___x_4577_, 0 as u32, v___x_4565_);
    lean_ctor_set_uint8(v___x_4577_, 1 as u32, v___x_4565_);
    v___x_4578_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4578_, 0, v___x_4577_);
    return v___x_4578_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed(
    mut v___x_4579_: *mut LeanObject,
    mut v_x_4580_: *mut LeanObject,
    mut v___y_4581_: *mut LeanObject,
    mut v___y_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_24024__boxed_4591_: u8 = 0;
    let mut v_res_4592_: *mut LeanObject = core::ptr::null_mut();
    v___x_24024__boxed_4591_ = (lean_unbox(v___x_4579_) as u8);
    v_res_4592_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1(
            v___x_24024__boxed_4591_,
            v_x_4580_,
            v___y_4581_,
            v___y_4582_,
            v___y_4583_,
            v___y_4584_,
            v___y_4585_,
            v___y_4586_,
            v___y_4587_,
            v___y_4588_,
            v___y_4589_,
        );
    lean_dec(v___y_4589_);
    lean_dec_ref(v___y_4588_);
    lean_dec(v___y_4587_);
    lean_dec_ref(v___y_4586_);
    lean_dec(v___y_4585_);
    lean_dec_ref(v___y_4584_);
    lean_dec(v___y_4583_);
    lean_dec_ref(v___y_4582_);
    lean_dec(v___y_4581_);
    lean_dec_ref(v_x_4580_);
    return v_res_4592_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(
    mut v___x_4595_: *mut LeanObject,
    mut v_argKinds_4596_: *mut LeanObject,
    mut v_mkNonRflResult_4597_: *mut LeanObject,
    mut v_x_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
    mut v___y_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    v___x_4609_ = lean_unsigned_to_nat(1);
    v___x_4610_ = lean_nat_sub(v___x_4595_, v___x_4609_);
    v___x_4611_ = lean_unsigned_to_nat(0);
    v___x_4612_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
    v___x_4613_ = 0;
    v___x_4614_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(
            v_argKinds_4596_,
            v_mkNonRflResult_4597_,
            v_x_4598_,
            v___x_4610_,
            v___x_4611_,
            v___x_4612_,
            v___x_4613_,
            v___y_4599_,
            v___y_4600_,
            v___y_4601_,
            v___y_4602_,
            v___y_4603_,
            v___y_4604_,
            v___y_4605_,
            v___y_4606_,
            v___y_4607_,
        );
    return v___x_4614_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed(
    mut v___x_4615_: *mut LeanObject,
    mut v_argKinds_4616_: *mut LeanObject,
    mut v_mkNonRflResult_4617_: *mut LeanObject,
    mut v_x_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
    mut v___y_4622_: *mut LeanObject,
    mut v___y_4623_: *mut LeanObject,
    mut v___y_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4629_: *mut LeanObject = core::ptr::null_mut();
    v_res_4629_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2(
            v___x_4615_,
            v_argKinds_4616_,
            v_mkNonRflResult_4617_,
            v_x_4618_,
            v___y_4619_,
            v___y_4620_,
            v___y_4621_,
            v___y_4622_,
            v___y_4623_,
            v___y_4624_,
            v___y_4625_,
            v___y_4626_,
            v___y_4627_,
        );
    lean_dec(v___y_4627_);
    lean_dec_ref(v___y_4626_);
    lean_dec(v___y_4625_);
    lean_dec_ref(v___y_4624_);
    lean_dec(v___y_4623_);
    lean_dec_ref(v___y_4622_);
    lean_dec(v___y_4621_);
    lean_dec_ref(v___y_4620_);
    lean_dec(v___y_4619_);
    lean_dec_ref(v_argKinds_4616_);
    lean_dec(v___x_4615_);
    return v_res_4629_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(
    mut v_e_4630_: *mut LeanObject,
    mut v_thm_4631_: *mut LeanObject,
    mut v_a_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
    mut v_a_4635_: *mut LeanObject,
    mut v_a_4636_: *mut LeanObject,
    mut v_a_4637_: *mut LeanObject,
    mut v_a_4638_: *mut LeanObject,
    mut v_a_4639_: *mut LeanObject,
    mut v_a_4640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argKinds_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mkNonRflResult_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numArgs_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: u8 = 0;
    v_type_4642_ = lean_ctor_get(v_thm_4631_, 0);
    lean_inc_ref(v_type_4642_);
    v_proof_4643_ = lean_ctor_get(v_thm_4631_, 1);
    lean_inc_ref(v_proof_4643_);
    v_argKinds_4644_ = lean_ctor_get(v_thm_4631_, 2);
    lean_inc_ref_n(v_argKinds_4644_, 2);
    lean_dec_ref(v_thm_4631_);
    lean_inc_ref(v_e_4630_);
    v_mkNonRflResult_4645_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__0___boxed
            as *mut core::ffi::c_void,
        15,
        4,
    );
    lean_closure_set(v_mkNonRflResult_4645_, 0, v_e_4630_);
    lean_closure_set(v_mkNonRflResult_4645_, 1, v_argKinds_4644_);
    lean_closure_set(v_mkNonRflResult_4645_, 2, v_type_4642_);
    lean_closure_set(v_mkNonRflResult_4645_, 3, v_proof_4643_);
    v_numArgs_4646_ = l_Lean_Expr_getAppNumArgs(v_e_4630_);
    v___x_4647_ = lean_array_get_size(v_argKinds_4644_);
    v___x_4648_ = lean_nat_dec_lt(v___x_4647_, v_numArgs_4646_);
    if v___x_4648_ == 0 {
        let mut v___x_4649_: u8 = 0;
        v___x_4649_ = lean_nat_dec_lt(v_numArgs_4646_, v___x_4647_);
        if v___x_4649_ == 0 {
            let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_numArgs_4646_);
            v___x_4650_ = lean_unsigned_to_nat(1);
            v___x_4651_ = lean_nat_sub(v___x_4647_, v___x_4650_);
            v___x_4652_ = lean_unsigned_to_nat(0);
            v___x_4653_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___closed__0;
            v___x_4654_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm_simpEqArgs(v_argKinds_4644_, v_mkNonRflResult_4645_, v_e_4630_, v___x_4651_, v___x_4652_, v___x_4653_, v___x_4649_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
            lean_dec_ref(v_argKinds_4644_);
            return v___x_4654_;
        } else {
            let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4656_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_mkNonRflResult_4645_);
            lean_dec_ref(v_argKinds_4644_);
            v___x_4655_ = lean_box((v___x_4648_) as usize);
            v___f_4656_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__1___boxed as *mut core::ffi::c_void, 12, 1);
            lean_closure_set(v___f_4656_, 0, v___x_4655_);
            v___x_4657_ =
                l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(
                    v___f_4656_,
                    v_e_4630_,
                    v_numArgs_4646_,
                    v_a_4632_,
                    v_a_4633_,
                    v_a_4634_,
                    v_a_4635_,
                    v_a_4636_,
                    v_a_4637_,
                    v_a_4638_,
                    v_a_4639_,
                    v_a_4640_,
                );
            lean_dec(v_numArgs_4646_);
            return v___x_4657_;
        }
    } else {
        let mut v___f_4658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
        v___f_4658_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___lam__2___boxed as *mut core::ffi::c_void, 14, 3);
        lean_closure_set(v___f_4658_, 0, v___x_4647_);
        lean_closure_set(v___f_4658_, 1, v_argKinds_4644_);
        lean_closure_set(v___f_4658_, 2, v_mkNonRflResult_4645_);
        v___x_4659_ = lean_nat_sub(v_numArgs_4646_, v___x_4647_);
        lean_dec(v_numArgs_4646_);
        v___x_4660_ =
            l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit(
                v___f_4658_,
                v_e_4630_,
                v___x_4659_,
                v_a_4632_,
                v_a_4633_,
                v_a_4634_,
                v_a_4635_,
                v_a_4636_,
                v_a_4637_,
                v_a_4638_,
                v_a_4639_,
                v_a_4640_,
            );
        lean_dec(v___x_4659_);
        return v___x_4660_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm___boxed(
    mut v_e_4661_: *mut LeanObject,
    mut v_thm_4662_: *mut LeanObject,
    mut v_a_4663_: *mut LeanObject,
    mut v_a_4664_: *mut LeanObject,
    mut v_a_4665_: *mut LeanObject,
    mut v_a_4666_: *mut LeanObject,
    mut v_a_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
    mut v_a_4669_: *mut LeanObject,
    mut v_a_4670_: *mut LeanObject,
    mut v_a_4671_: *mut LeanObject,
    mut v_a_4672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4673_: *mut LeanObject = core::ptr::null_mut();
    v_res_4673_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(
        v_e_4661_,
        v_thm_4662_,
        v_a_4663_,
        v_a_4664_,
        v_a_4665_,
        v_a_4666_,
        v_a_4667_,
        v_a_4668_,
        v_a_4669_,
        v_a_4670_,
        v_a_4671_,
    );
    lean_dec(v_a_4671_);
    lean_dec_ref(v_a_4670_);
    lean_dec(v_a_4669_);
    lean_dec_ref(v_a_4668_);
    lean_dec(v_a_4667_);
    lean_dec_ref(v_a_4666_);
    lean_dec(v_a_4665_);
    lean_dec_ref(v_a_4664_);
    lean_dec(v_a_4663_);
    return v_res_4673_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpAppArgs(
    mut v_e_4674_: *mut LeanObject,
    mut v_a_4675_: *mut LeanObject,
    mut v_a_4676_: *mut LeanObject,
    mut v_a_4677_: *mut LeanObject,
    mut v_a_4678_: *mut LeanObject,
    mut v_a_4679_: *mut LeanObject,
    mut v_a_4680_: *mut LeanObject,
    mut v_a_4681_: *mut LeanObject,
    mut v_a_4682_: *mut LeanObject,
    mut v_a_4683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4690_: u8 = 0;
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prefixSize_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suffixSize_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rewritable_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thm_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut v_a_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_f_4685_ = l_Lean_Expr_getAppFn(v_e_4674_);
                v___x_4686_ = l_Lean_Meta_Sym_getCongrInfo___redArg(
                    v_f_4685_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_,
                );
                if lean_obj_tag(v___x_4686_) == 0 {
                    v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
                    v_isSharedCheck_4702_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4702_ == 0 {
                        v___x_4689_ = v___x_4686_;
                        v_isShared_4690_ = v_isSharedCheck_4702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4687_);
                        lean_dec(v___x_4686_);
                        v___x_4689_ = lean_box(0);
                        v_isShared_4690_ = v_isSharedCheck_4702_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4674_);
                    v_a_4703_ = lean_ctor_get(v___x_4686_, 0);
                    v_isSharedCheck_4710_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4710_ == 0 {
                        v___x_4705_ = v___x_4686_;
                        v_isShared_4706_ = v_isSharedCheck_4710_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4703_);
                        lean_dec(v___x_4686_);
                        v___x_4705_ = lean_box(0);
                        v_isShared_4706_ = v_isSharedCheck_4710_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                match lean_obj_tag(v_a_4687_) {
                    0 => {
                        lean_dec_ref(v_e_4674_);
                        v___x_4691_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
                        if v_isShared_4690_ == 0 {
                            lean_ctor_set(v___x_4689_, 0, v___x_4691_);
                            v___x_4693_ = v___x_4689_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
                            v___x_4693_ = v_reuseFailAlloc_4694_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        lean_del_object(v___x_4689_);
                        v_prefixSize_4695_ = lean_ctor_get(v_a_4687_, 0);
                        lean_inc(v_prefixSize_4695_);
                        v_suffixSize_4696_ = lean_ctor_get(v_a_4687_, 1);
                        lean_inc(v_suffixSize_4696_);
                        lean_dec_ref_known(v_a_4687_, 2);
                        v___x_4697_ = l_Lean_Meta_Sym_Simp_simpFixedPrefix(
                            v_e_4674_,
                            v_prefixSize_4695_,
                            v_suffixSize_4696_,
                            v_a_4675_,
                            v_a_4676_,
                            v_a_4677_,
                            v_a_4678_,
                            v_a_4679_,
                            v_a_4680_,
                            v_a_4681_,
                            v_a_4682_,
                            v_a_4683_,
                        );
                        lean_dec(v_prefixSize_4695_);
                        return v___x_4697_;
                    }
                    2 => {
                        lean_del_object(v___x_4689_);
                        v_rewritable_4698_ = lean_ctor_get(v_a_4687_, 0);
                        lean_inc_ref(v_rewritable_4698_);
                        lean_dec_ref_known(v_a_4687_, 1);
                        v___x_4699_ = l_Lean_Meta_Sym_Simp_simpInterlaced(
                            v_e_4674_,
                            v_rewritable_4698_,
                            v_a_4675_,
                            v_a_4676_,
                            v_a_4677_,
                            v_a_4678_,
                            v_a_4679_,
                            v_a_4680_,
                            v_a_4681_,
                            v_a_4682_,
                            v_a_4683_,
                        );
                        return v___x_4699_;
                    }
                    _ => {
                        lean_del_object(v___x_4689_);
                        v_thm_4700_ = lean_ctor_get(v_a_4687_, 0);
                        lean_inc_ref(v_thm_4700_);
                        lean_dec_ref_known(v_a_4687_, 1);
                        v___x_4701_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpUsingCongrThm(v_e_4674_, v_thm_4700_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
                        return v___x_4701_;
                    }
                }
            }
            2 => {
                return v___x_4693_;
            }
            3 => {
                if v_isShared_4706_ == 0 {
                    v___x_4708_ = v___x_4705_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
                    v___x_4708_ = v_reuseFailAlloc_4709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpAppArgs___boxed(
    mut v_e_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
    mut v_a_4713_: *mut LeanObject,
    mut v_a_4714_: *mut LeanObject,
    mut v_a_4715_: *mut LeanObject,
    mut v_a_4716_: *mut LeanObject,
    mut v_a_4717_: *mut LeanObject,
    mut v_a_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4722_: *mut LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_Meta_Sym_Simp_simpAppArgs(
        v_e_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_,
        v_a_4719_, v_a_4720_,
    );
    lean_dec(v_a_4720_);
    lean_dec_ref(v_a_4719_);
    lean_dec(v_a_4718_);
    lean_dec_ref(v_a_4717_);
    lean_dec(v_a_4716_);
    lean_dec_ref(v_a_4715_);
    lean_dec(v_a_4714_);
    lean_dec_ref(v_a_4713_);
    lean_dec(v_a_4712_);
    return v_res_4722_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1()
-> *mut LeanObject {
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    v___x_4724_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_4725_ = lean_unsigned_to_nat(55);
    v___x_4726_ = lean_unsigned_to_nat(489);
    v___x_4727_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0;
    v___x_4728_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_4729_ = l_mkPanicMessageWithDecl(
        v___x_4728_,
        v___x_4727_,
        v___x_4726_,
        v___x_4725_,
        v___x_4724_,
    );
    return v___x_4729_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2()
-> *mut LeanObject {
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    v___x_4730_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__2;
    v___x_4731_ = lean_unsigned_to_nat(11);
    v___x_4732_ = lean_unsigned_to_nat(497);
    v___x_4733_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__0;
    v___x_4734_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_4735_ = l_mkPanicMessageWithDecl(
        v___x_4734_,
        v___x_4733_,
        v___x_4732_,
        v___x_4731_,
        v___x_4730_,
    );
    return v___x_4735_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(
    mut v_stop_4736_: *mut LeanObject,
    mut v_e_4737_: *mut LeanObject,
    mut v_i_4738_: *mut LeanObject,
    mut v_a_4739_: *mut LeanObject,
    mut v_a_4740_: *mut LeanObject,
    mut v_a_4741_: *mut LeanObject,
    mut v_a_4742_: *mut LeanObject,
    mut v_a_4743_: *mut LeanObject,
    mut v_a_4744_: *mut LeanObject,
    mut v_a_4745_: *mut LeanObject,
    mut v_a_4746_: *mut LeanObject,
    mut v_a_4747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cd_4750_: u8 = 0;
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: u8 = 0;
    let mut v_fn_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: u8 = 0;
    let mut v_contextDependent_4762_: u8 = 0;
    let mut v_e_x27_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4765_: u8 = 0;
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: u8 = 0;
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4785_: u8 = 0;
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4789_: u8 = 0;
    let mut v___x_4790_: u8 = 0;
    let mut v_contextDependent_4791_: u8 = 0;
    let mut v_e_x27_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4794_: u8 = 0;
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4805_: u8 = 0;
    let mut v_a_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4809_: u8 = 0;
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4813_: u8 = 0;
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4753_ = lean_unsigned_to_nat(0);
                v___x_4754_ = lean_nat_dec_eq(v_i_4738_, v___x_4753_);
                if v___x_4754_ == 0 {
                    if lean_obj_tag(v_e_4737_) == 5 {
                        v_fn_4755_ = lean_ctor_get(v_e_4737_, 0);
                        lean_inc_ref_n(v_fn_4755_, 2);
                        v_arg_4756_ = lean_ctor_get(v_e_4737_, 1);
                        lean_inc_ref(v_arg_4756_);
                        v___x_4757_ = lean_unsigned_to_nat(1);
                        v_i_4758_ = lean_nat_sub(v_i_4738_, v___x_4757_);
                        v___x_4759_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(v_stop_4736_, v_fn_4755_, v_i_4758_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
                        if lean_obj_tag(v___x_4759_) == 0 {
                            v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
                            lean_inc(v_a_4760_);
                            lean_dec_ref_known(v___x_4759_, 1);
                            v___x_4761_ = lean_nat_dec_lt(v_i_4758_, v_stop_4736_);
                            lean_dec(v_i_4758_);
                            if v___x_4761_ == 0 {
                                if lean_obj_tag(v_a_4760_) == 0 {
                                    lean_dec_ref(v_arg_4756_);
                                    lean_dec_ref_known(v_e_4737_, 2);
                                    lean_dec_ref(v_fn_4755_);
                                    v_contextDependent_4762_ =
                                        lean_ctor_get_uint8(v_a_4760_, 1 as u32);
                                    lean_dec_ref_known(v_a_4760_, 0);
                                    v_cd_4750_ = v_contextDependent_4762_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_e_x27_4763_ = lean_ctor_get(v_a_4760_, 0);
                                    lean_inc_ref(v_e_x27_4763_);
                                    v_proof_4764_ = lean_ctor_get(v_a_4760_, 1);
                                    lean_inc_ref(v_proof_4764_);
                                    v_contextDependent_4765_ = lean_ctor_get_uint8(
                                        v_a_4760_,
                                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                                    );
                                    lean_dec_ref_known(v_a_4760_, 2);
                                    v___x_4766_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_4737_, v_fn_4755_, v_arg_4756_, v_e_x27_4763_, v_proof_4764_, v___x_4754_, v_contextDependent_4765_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
                                    return v___x_4766_;
                                }
                            } else {
                                lean_inc_ref(v_fn_4755_);
                                v___x_4767_ = l_Lean_Meta_Sym_inferType___redArg(
                                    v_fn_4755_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_,
                                    v_a_4747_,
                                );
                                if lean_obj_tag(v___x_4767_) == 0 {
                                    v_a_4768_ = lean_ctor_get(v___x_4767_, 0);
                                    lean_inc(v_a_4768_);
                                    lean_dec_ref_known(v___x_4767_, 1);
                                    v___x_4769_ = l_Lean_Meta_whnfD(
                                        v_a_4768_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_,
                                    );
                                    if lean_obj_tag(v___x_4769_) == 0 {
                                        v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
                                        lean_inc(v_a_4770_);
                                        lean_dec_ref_known(v___x_4769_, 1);
                                        if lean_obj_tag(v_a_4770_) == 7 {
                                            v_binderType_4771_ = lean_ctor_get(v_a_4770_, 1);
                                            lean_inc_ref(v_binderType_4771_);
                                            v_body_4772_ = lean_ctor_get(v_a_4770_, 2);
                                            lean_inc_ref(v_body_4772_);
                                            lean_dec_ref_known(v_a_4770_, 3);
                                            v___x_4790_ = l_Lean_Expr_hasLooseBVars(v_body_4772_);
                                            lean_dec_ref(v_body_4772_);
                                            if v___x_4790_ == 0 {
                                                state = 2;
                                                continue;
                                            } else {
                                                if v___x_4754_ == 0 {
                                                    lean_dec_ref(v_binderType_4771_);
                                                    if lean_obj_tag(v_a_4760_) == 0 {
                                                        lean_dec_ref(v_arg_4756_);
                                                        lean_dec_ref_known(v_e_4737_, 2);
                                                        lean_dec_ref(v_fn_4755_);
                                                        v_contextDependent_4791_ =
                                                            lean_ctor_get_uint8(
                                                                v_a_4760_, 1 as u32,
                                                            );
                                                        lean_dec_ref_known(v_a_4760_, 0);
                                                        v_cd_4750_ = v_contextDependent_4791_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v_e_x27_4792_ = lean_ctor_get(v_a_4760_, 0);
                                                        lean_inc_ref(v_e_x27_4792_);
                                                        v_proof_4793_ = lean_ctor_get(v_a_4760_, 1);
                                                        lean_inc_ref(v_proof_4793_);
                                                        v_contextDependent_4794_ =
                                                            lean_ctor_get_uint8(
                                                                v_a_4760_,
                                                                (core::mem::size_of::<
                                                                    *mut LeanObject,
                                                                >(
                                                                ) * 2
                                                                    + 1)
                                                                    as u32,
                                                            );
                                                        lean_dec_ref_known(v_a_4760_, 2);
                                                        v___x_4795_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(v_e_4737_, v_fn_4755_, v_arg_4756_, v_e_x27_4792_, v_proof_4793_, v___x_4754_, v_contextDependent_4794_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
                                                        return v___x_4795_;
                                                    }
                                                } else {
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_4770_);
                                            lean_dec(v_a_4760_);
                                            lean_dec_ref(v_arg_4756_);
                                            lean_dec_ref_known(v_e_4737_, 2);
                                            lean_dec_ref(v_fn_4755_);
                                            v___x_4796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__1);
                                            v___x_4797_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_4796_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
                                            return v___x_4797_;
                                        }
                                    } else {
                                        lean_dec(v_a_4760_);
                                        lean_dec_ref(v_arg_4756_);
                                        lean_dec_ref_known(v_e_4737_, 2);
                                        lean_dec_ref(v_fn_4755_);
                                        v_a_4798_ = lean_ctor_get(v___x_4769_, 0);
                                        v_isSharedCheck_4805_ =
                                            (!lean_is_exclusive(v___x_4769_)) as u8;
                                        if v_isSharedCheck_4805_ == 0 {
                                            v___x_4800_ = v___x_4769_;
                                            v_isShared_4801_ = v_isSharedCheck_4805_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4798_);
                                            lean_dec(v___x_4769_);
                                            v___x_4800_ = lean_box(0);
                                            v_isShared_4801_ = v_isSharedCheck_4805_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_4760_);
                                    lean_dec_ref(v_arg_4756_);
                                    lean_dec_ref_known(v_e_4737_, 2);
                                    lean_dec_ref(v_fn_4755_);
                                    v_a_4806_ = lean_ctor_get(v___x_4767_, 0);
                                    v_isSharedCheck_4813_ = (!lean_is_exclusive(v___x_4767_)) as u8;
                                    if v_isSharedCheck_4813_ == 0 {
                                        v___x_4808_ = v___x_4767_;
                                        v_isShared_4809_ = v_isSharedCheck_4813_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4806_);
                                        lean_dec(v___x_4767_);
                                        v___x_4808_ = lean_box(0);
                                        v_isShared_4809_ = v_isSharedCheck_4813_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_i_4758_);
                            lean_dec_ref(v_arg_4756_);
                            lean_dec_ref(v_fn_4755_);
                            lean_dec_ref_known(v_e_4737_, 2);
                            return v___x_4759_;
                        }
                    } else {
                        lean_dec_ref(v_e_4737_);
                        v___x_4814_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___closed__2);
                        v___x_4815_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_4814_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
                        return v___x_4815_;
                    }
                } else {
                    lean_dec_ref(v_e_4737_);
                    v___x_4816_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
                    v___x_4817_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4817_, 0, v___x_4816_);
                    return v___x_4817_;
                }
            }
            1 => {
                v___x_4751_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_cd_4750_);
                v___x_4752_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4752_, 0, v___x_4751_);
                return v___x_4752_;
            }
            2 => {
                v___x_4774_ = l_Lean_Meta_isProp(
                    v_binderType_4771_,
                    v_a_4744_,
                    v_a_4745_,
                    v_a_4746_,
                    v_a_4747_,
                );
                if lean_obj_tag(v___x_4774_) == 0 {
                    v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
                    lean_inc(v_a_4775_);
                    lean_dec_ref_known(v___x_4774_, 1);
                    v___x_4776_ = (lean_unbox(v_a_4775_) as u8);
                    lean_dec(v_a_4775_);
                    if v___x_4776_ == 0 {
                        lean_inc(v_a_4747_);
                        lean_inc_ref(v_a_4746_);
                        lean_inc(v_a_4745_);
                        lean_inc_ref(v_a_4744_);
                        lean_inc(v_a_4743_);
                        lean_inc_ref(v_a_4742_);
                        lean_inc(v_a_4741_);
                        lean_inc_ref(v_a_4740_);
                        lean_inc(v_a_4739_);
                        lean_inc_ref(v_arg_4756_);
                        v___x_4777_ = lean_sym_simp(
                            v_arg_4756_,
                            v_a_4739_,
                            v_a_4740_,
                            v_a_4741_,
                            v_a_4742_,
                            v_a_4743_,
                            v_a_4744_,
                            v_a_4745_,
                            v_a_4746_,
                            v_a_4747_,
                        );
                        if lean_obj_tag(v___x_4777_) == 0 {
                            v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
                            lean_inc(v_a_4778_);
                            lean_dec_ref_known(v___x_4777_, 1);
                            v___x_4779_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(
                                v_e_4737_,
                                v_fn_4755_,
                                v_arg_4756_,
                                v_a_4760_,
                                v_a_4778_,
                                v_a_4742_,
                                v_a_4743_,
                                v_a_4744_,
                                v_a_4745_,
                                v_a_4746_,
                                v_a_4747_,
                            );
                            return v___x_4779_;
                        } else {
                            lean_dec(v_a_4760_);
                            lean_dec_ref(v_arg_4756_);
                            lean_dec_ref_known(v_e_4737_, 2);
                            lean_dec_ref(v_fn_4755_);
                            return v___x_4777_;
                        }
                    } else {
                        v___x_4780_ = lean_alloc_ctor(0, 0, (2) as u32);
                        lean_ctor_set_uint8(v___x_4780_, 0 as u32, v___x_4754_);
                        lean_ctor_set_uint8(v___x_4780_, 1 as u32, v___x_4754_);
                        v___x_4781_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(
                            v_e_4737_,
                            v_fn_4755_,
                            v_arg_4756_,
                            v_a_4760_,
                            v___x_4780_,
                            v_a_4742_,
                            v_a_4743_,
                            v_a_4744_,
                            v_a_4745_,
                            v_a_4746_,
                            v_a_4747_,
                        );
                        return v___x_4781_;
                    }
                } else {
                    lean_dec(v_a_4760_);
                    lean_dec_ref(v_arg_4756_);
                    lean_dec_ref_known(v_e_4737_, 2);
                    lean_dec_ref(v_fn_4755_);
                    v_a_4782_ = lean_ctor_get(v___x_4774_, 0);
                    v_isSharedCheck_4789_ = (!lean_is_exclusive(v___x_4774_)) as u8;
                    if v_isSharedCheck_4789_ == 0 {
                        v___x_4784_ = v___x_4774_;
                        v_isShared_4785_ = v_isSharedCheck_4789_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4782_);
                        lean_dec(v___x_4774_);
                        v___x_4784_ = lean_box(0);
                        v_isShared_4785_ = v_isSharedCheck_4789_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4785_ == 0 {
                    v___x_4787_ = v___x_4784_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
                    v___x_4787_ = v_reuseFailAlloc_4788_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4787_;
            }
            5 => {
                if v_isShared_4801_ == 0 {
                    v___x_4803_ = v___x_4800_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
                    v___x_4803_ = v_reuseFailAlloc_4804_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4803_;
            }
            7 => {
                if v_isShared_4809_ == 0 {
                    v___x_4811_ = v___x_4808_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
                    v___x_4811_ = v_reuseFailAlloc_4812_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit___boxed(
    mut v_stop_4818_: *mut LeanObject,
    mut v_e_4819_: *mut LeanObject,
    mut v_i_4820_: *mut LeanObject,
    mut v_a_4821_: *mut LeanObject,
    mut v_a_4822_: *mut LeanObject,
    mut v_a_4823_: *mut LeanObject,
    mut v_a_4824_: *mut LeanObject,
    mut v_a_4825_: *mut LeanObject,
    mut v_a_4826_: *mut LeanObject,
    mut v_a_4827_: *mut LeanObject,
    mut v_a_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
    mut v_a_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4831_: *mut LeanObject = core::ptr::null_mut();
    v_res_4831_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(
        v_stop_4818_,
        v_e_4819_,
        v_i_4820_,
        v_a_4821_,
        v_a_4822_,
        v_a_4823_,
        v_a_4824_,
        v_a_4825_,
        v_a_4826_,
        v_a_4827_,
        v_a_4828_,
        v_a_4829_,
    );
    lean_dec(v_a_4829_);
    lean_dec_ref(v_a_4828_);
    lean_dec(v_a_4827_);
    lean_dec_ref(v_a_4826_);
    lean_dec(v_a_4825_);
    lean_dec_ref(v_a_4824_);
    lean_dec(v_a_4823_);
    lean_dec_ref(v_a_4822_);
    lean_dec(v_a_4821_);
    lean_dec(v_i_4820_);
    lean_dec(v_stop_4818_);
    return v_res_4831_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2() -> *mut LeanObject {
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    v___x_4834_ = l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__1;
    v___x_4835_ = lean_unsigned_to_nat(2);
    v___x_4836_ = lean_unsigned_to_nat(472);
    v___x_4837_ = l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__0;
    v___x_4838_ =
        l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit___closed__0;
    v___x_4839_ = l_mkPanicMessageWithDecl(
        v___x_4838_,
        v___x_4837_,
        v___x_4836_,
        v___x_4835_,
        v___x_4834_,
    );
    return v___x_4839_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpAppArgRange(
    mut v_e_4840_: *mut LeanObject,
    mut v_start_4841_: *mut LeanObject,
    mut v_stop_4842_: *mut LeanObject,
    mut v_a_4843_: *mut LeanObject,
    mut v_a_4844_: *mut LeanObject,
    mut v_a_4845_: *mut LeanObject,
    mut v_a_4846_: *mut LeanObject,
    mut v_a_4847_: *mut LeanObject,
    mut v_a_4848_: *mut LeanObject,
    mut v_a_4849_: *mut LeanObject,
    mut v_a_4850_: *mut LeanObject,
    mut v_a_4851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4853_: u8 = 0;
    v___x_4853_ = lean_nat_dec_lt(v_start_4841_, v_stop_4842_);
    if v___x_4853_ == 0 {
        let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_4840_);
        v___x_4854_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2_once),
            _init_l_Lean_Meta_Sym_Simp_simpAppArgRange___closed__2,
        );
        v___x_4855_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpOverApplied_visit_spec__0(v___x_4854_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
        return v___x_4855_;
    } else {
        let mut v_numArgs_4856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4857_: u8 = 0;
        v_numArgs_4856_ = l_Lean_Expr_getAppNumArgs(v_e_4840_);
        v___x_4857_ = lean_nat_dec_lt(v_numArgs_4856_, v_start_4841_);
        if v___x_4857_ == 0 {
            let mut v_numArgs_4858_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stop_4859_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
            v_numArgs_4858_ = lean_nat_sub(v_numArgs_4856_, v_start_4841_);
            lean_dec(v_numArgs_4856_);
            v_stop_4859_ = lean_nat_sub(v_stop_4842_, v_start_4841_);
            v___x_4860_ =
                l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpAppArgRange_visit(
                    v_stop_4859_,
                    v_e_4840_,
                    v_numArgs_4858_,
                    v_a_4843_,
                    v_a_4844_,
                    v_a_4845_,
                    v_a_4846_,
                    v_a_4847_,
                    v_a_4848_,
                    v_a_4849_,
                    v_a_4850_,
                    v_a_4851_,
                );
            lean_dec(v_numArgs_4858_);
            lean_dec(v_stop_4859_);
            return v___x_4860_;
        } else {
            let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_numArgs_4856_);
            lean_dec_ref(v_e_4840_);
            v___x_4861_ = l___private_Lean_Meta_Sym_Simp_App_0__Lean_Meta_Sym_Simp_simpFixedPrefix_go___closed__8;
            v___x_4862_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_4862_, 0, v___x_4861_);
            return v___x_4862_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpAppArgRange___boxed(
    mut v_e_4863_: *mut LeanObject,
    mut v_start_4864_: *mut LeanObject,
    mut v_stop_4865_: *mut LeanObject,
    mut v_a_4866_: *mut LeanObject,
    mut v_a_4867_: *mut LeanObject,
    mut v_a_4868_: *mut LeanObject,
    mut v_a_4869_: *mut LeanObject,
    mut v_a_4870_: *mut LeanObject,
    mut v_a_4871_: *mut LeanObject,
    mut v_a_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
    mut v_a_4874_: *mut LeanObject,
    mut v_a_4875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4876_: *mut LeanObject = core::ptr::null_mut();
    v_res_4876_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(
        v_e_4863_,
        v_start_4864_,
        v_stop_4865_,
        v_a_4866_,
        v_a_4867_,
        v_a_4868_,
        v_a_4869_,
        v_a_4870_,
        v_a_4871_,
        v_a_4872_,
        v_a_4873_,
        v_a_4874_,
    );
    lean_dec(v_a_4874_);
    lean_dec_ref(v_a_4873_);
    lean_dec(v_a_4872_);
    lean_dec_ref(v_a_4871_);
    lean_dec(v_a_4870_);
    lean_dec_ref(v_a_4869_);
    lean_dec(v_a_4868_);
    lean_dec_ref(v_a_4867_);
    lean_dec(v_a_4866_);
    lean_dec(v_stop_4865_);
    lean_dec(v_start_4864_);
    return v_res_4876_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_App(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_App(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_App(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_App(builtin);
}

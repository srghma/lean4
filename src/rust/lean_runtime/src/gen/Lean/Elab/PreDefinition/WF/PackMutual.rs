// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.PackMutual
// Imports: Lean.Meta.ArgsPacker Lean.Elab.PreDefinition.WF.Eqns
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_maxRecDepthErrorMessage,
};
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::PreDefinition::Basic::{
    l_Lean_Elab_addAsAxiom___redArg, l_Lean_Elab_instInhabitedPreDefinition_default,
};
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl,
    l_Lean_Elab_FixedParamPerm_instantiateForall, l_Lean_Elab_FixedParamPerm_instantiateLambda,
    l_Lean_Elab_FixedParamPerm_pickFixed___redArg, l_Lean_Elab_FixedParamPerm_pickVarying___redArg,
    l_Lean_Elab_FixedParamPerms_fixedArePrefix,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::Eqns::{
    initialize_Lean_Elab_PreDefinition_WF_Eqns, runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_unlockAsync;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override, l_Lean_Expr_beta,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_constName_x21, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConst, l_Lean_Expr_isForall,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::ArgsPacker::{
    initialize_Lean_Meta_ArgsPacker, l_Lean_Meta_ArgsPacker_curryProj,
    l_Lean_Meta_ArgsPacker_numFuncs, l_Lean_Meta_ArgsPacker_onlyOneUnary,
    l_Lean_Meta_ArgsPacker_pack, l_Lean_Meta_ArgsPacker_uncurry,
    l_Lean_Meta_ArgsPacker_uncurryType, runtime_initialize_Lean_Meta_ArgsPacker,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_FVarId_getUserName___redArg,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
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
    lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate_rev;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_5, lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_WF_withAppN___lam__0___closed__0_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 116, 97, 45, 101, 120, 112, 97, 110,
            100, 32, 112, 97, 114, 116, 105, 97, 108, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105,
            111, 110, 0,
        ],
    };
static mut l_Lean_Elab_WF_withAppN___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_withAppN___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_WF_withAppN___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_withAppN___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_WF_withAppN___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_withAppN___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_WF_packCalls___lam__0___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_WF_packCalls___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_packCalls___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_packCalls___lam__2___closed__0_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105,
            116, 105, 111, 110, 46, 87, 70, 46, 80, 97, 99, 107, 77, 117, 116, 117, 97, 108, 0,
        ],
    };
static mut l_Lean_Elab_WF_packCalls___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_packCalls___lam__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_packCalls___lam__2___closed__1_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 87, 70, 46, 112, 97, 99, 107, 67, 97, 108,
            108, 115, 0,
        ],
    };
static mut l_Lean_Elab_WF_packCalls___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_packCalls___lam__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_packCalls___lam__2___closed__2_value: LeanStringObject<62> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 62,
        m_capacity: 62,
        m_length: 61,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 102, 105, 100, 120, 32, 60, 32, 102, 105, 120, 101, 100, 80, 97, 114, 97,
            109, 80, 101, 114, 109, 115, 46, 112, 101, 114, 109, 115, 46, 115, 105, 122, 101, 10,
            32, 32, 32, 32, 32, 32, 0,
        ],
    };
static mut l_Lean_Elab_WF_packCalls___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_packCalls___lam__2___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_WF_packCalls___lam__2___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_packCalls___lam__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_WF_packCalls___lam__2___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_packCalls___lam__2___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_WF_packCalls___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_WF_packCalls___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_WF_packCalls___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_packCalls___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_packCalls___closed__1_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        78, 111, 116, 32, 97, 32, 102, 111, 114, 97, 108, 108, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_WF_packCalls___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_packCalls___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_WF_packCalls___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_packCalls___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_WF_packCalls___closed__3_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l_Lean_Elab_WF_packCalls___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_packCalls___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_WF_packCalls___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_packCalls___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_WF_mutualName___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [95, 117, 110, 97, 114, 121, 0],
};
static mut l_Lean_Elab_WF_mutualName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_mutualName___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_mutualName___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_WF_mutualName___closed__0_value) as *mut LeanObject,
        12659383327240972142 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_WF_mutualName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_mutualName___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_mutualName___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [95, 109, 117, 116, 117, 97, 108, 0],
};
static mut l_Lean_Elab_WF_mutualName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_mutualName___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_mutualName___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_WF_mutualName___closed__2_value) as *mut LeanObject,
        4264847933555826748 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_WF_mutualName___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_mutualName___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 87, 70, 46, 118, 97, 114, 121, 105, 110,
            103, 86, 97, 114, 78, 97, 109, 101, 115, 0,
        ],
    };
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 61, 32, 97, 114, 105, 116, 121, 10,
            32, 32, 32, 32, 0,
        ],
    };
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3_value: LeanStringObject<73> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 73,
        m_capacity: 73,
        m_length: 72,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 102, 105, 120, 101, 100, 80, 97, 114, 97, 109, 80, 101, 114, 109, 115, 46,
            112, 101, 114, 109, 115, 91, 112, 114, 101, 68, 101, 102, 73, 100, 120, 93, 33, 46,
            115, 105, 122, 101, 32, 61, 32, 97, 114, 105, 116, 121, 10, 32, 32, 32, 32, 0,
        ],
    };
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_WF_varyingVarNames___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_WF_varyingVarNames___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_WF_varyingVarNames___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_varyingVarNames___closed__0_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value
) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 87, 70, 46, 112, 114, 101, 68, 101, 102, 115, 70, 114, 111, 109, 85, 110, 97, 114, 121, 78, 111, 110, 82, 101, 99, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 97, 114, 105, 116, 121, 32, 61, 32, 112, 97, 114, 97, 109, 115, 46, 115, 105, 122, 101, 10, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [119, 102, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value) as *mut LeanObject,6897119537390546559 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value) as *mut LeanObject,16378770904461102315 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(
    mut v_k_3102_: *mut LeanObject,
    mut v_b_3103_: *mut LeanObject,
    mut v_c_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3108_);
    lean_inc_ref(v___y_3107_);
    lean_inc(v___y_3106_);
    lean_inc_ref(v___y_3105_);
    v___x_3110_ = lean_apply_7(
        v_k_3102_,
        v_b_3103_,
        v_c_3104_,
        v___y_3105_,
        v___y_3106_,
        v___y_3107_,
        v___y_3108_,
        lean_box(0),
    );
    return v___x_3110_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed(
    mut v_k_3111_: *mut LeanObject,
    mut v_b_3112_: *mut LeanObject,
    mut v_c_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
    mut v___y_3115_: *mut LeanObject,
    mut v___y_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3119_: *mut LeanObject = core::ptr::null_mut();
    v_res_3119_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(
            v_k_3111_,
            v_b_3112_,
            v_c_3113_,
            v___y_3114_,
            v___y_3115_,
            v___y_3116_,
            v___y_3117_,
        );
    lean_dec(v___y_3117_);
    lean_dec_ref(v___y_3116_);
    lean_dec(v___y_3115_);
    lean_dec_ref(v___y_3114_);
    return v_res_3119_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(
    mut v_type_3120_: *mut LeanObject,
    mut v_maxFVars_x3f_3121_: *mut LeanObject,
    mut v_k_3122_: *mut LeanObject,
    mut v_cleanupAnnotations_3123_: u8,
    mut v_whnfType_3124_: u8,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
    mut v___y_3127_: *mut LeanObject,
    mut v___y_3128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut v_a_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3130_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3130_, 0, v_k_3122_);
                v___x_3131_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_3120_,
                    v_maxFVars_x3f_3121_,
                    v___f_3130_,
                    v_cleanupAnnotations_3123_,
                    v_whnfType_3124_,
                    v___y_3125_,
                    v___y_3126_,
                    v___y_3127_,
                    v___y_3128_,
                );
                if lean_obj_tag(v___x_3131_) == 0 {
                    v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
                    v_isSharedCheck_3139_ = (!lean_is_exclusive(v___x_3131_)) as u8;
                    if v_isSharedCheck_3139_ == 0 {
                        v___x_3134_ = v___x_3131_;
                        v_isShared_3135_ = v_isSharedCheck_3139_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3132_);
                        lean_dec(v___x_3131_);
                        v___x_3134_ = lean_box(0);
                        v_isShared_3135_ = v_isSharedCheck_3139_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3140_ = lean_ctor_get(v___x_3131_, 0);
                    v_isSharedCheck_3147_ = (!lean_is_exclusive(v___x_3131_)) as u8;
                    if v_isSharedCheck_3147_ == 0 {
                        v___x_3142_ = v___x_3131_;
                        v_isShared_3143_ = v_isSharedCheck_3147_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3140_);
                        lean_dec(v___x_3131_);
                        v___x_3142_ = lean_box(0);
                        v_isShared_3143_ = v_isSharedCheck_3147_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3135_ == 0 {
                    v___x_3137_ = v___x_3134_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
                    v___x_3137_ = v_reuseFailAlloc_3138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3137_;
            }
            3 => {
                if v_isShared_3143_ == 0 {
                    v___x_3145_ = v___x_3142_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
                    v___x_3145_ = v_reuseFailAlloc_3146_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___boxed(
    mut v_type_3148_: *mut LeanObject,
    mut v_maxFVars_x3f_3149_: *mut LeanObject,
    mut v_k_3150_: *mut LeanObject,
    mut v_cleanupAnnotations_3151_: *mut LeanObject,
    mut v_whnfType_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
    mut v___y_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3158_: u8 = 0;
    let mut v_whnfType_boxed_3159_: u8 = 0;
    let mut v_res_3160_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3158_ = (lean_unbox(v_cleanupAnnotations_3151_) as u8);
    v_whnfType_boxed_3159_ = (lean_unbox(v_whnfType_3152_) as u8);
    v_res_3160_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(
            v_type_3148_,
            v_maxFVars_x3f_3149_,
            v_k_3150_,
            v_cleanupAnnotations_boxed_3158_,
            v_whnfType_boxed_3159_,
            v___y_3153_,
            v___y_3154_,
            v___y_3155_,
            v___y_3156_,
        );
    lean_dec(v___y_3156_);
    lean_dec_ref(v___y_3155_);
    lean_dec(v___y_3154_);
    lean_dec_ref(v___y_3153_);
    return v_res_3160_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(
    mut v_00_u03b1_3161_: *mut LeanObject,
    mut v_type_3162_: *mut LeanObject,
    mut v_maxFVars_x3f_3163_: *mut LeanObject,
    mut v_k_3164_: *mut LeanObject,
    mut v_cleanupAnnotations_3165_: u8,
    mut v_whnfType_3166_: u8,
    mut v___y_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    v___x_3172_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(
            v_type_3162_,
            v_maxFVars_x3f_3163_,
            v_k_3164_,
            v_cleanupAnnotations_3165_,
            v_whnfType_3166_,
            v___y_3167_,
            v___y_3168_,
            v___y_3169_,
            v___y_3170_,
        );
    return v___x_3172_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___boxed(
    mut v_00_u03b1_3173_: *mut LeanObject,
    mut v_type_3174_: *mut LeanObject,
    mut v_maxFVars_x3f_3175_: *mut LeanObject,
    mut v_k_3176_: *mut LeanObject,
    mut v_cleanupAnnotations_3177_: *mut LeanObject,
    mut v_whnfType_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
    mut v___y_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
    mut v___y_3183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3184_: u8 = 0;
    let mut v_whnfType_boxed_3185_: u8 = 0;
    let mut v_res_3186_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3184_ = (lean_unbox(v_cleanupAnnotations_3177_) as u8);
    v_whnfType_boxed_3185_ = (lean_unbox(v_whnfType_3178_) as u8);
    v_res_3186_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(
        v_00_u03b1_3173_,
        v_type_3174_,
        v_maxFVars_x3f_3175_,
        v_k_3176_,
        v_cleanupAnnotations_boxed_3184_,
        v_whnfType_boxed_3185_,
        v___y_3179_,
        v___y_3180_,
        v___y_3181_,
        v___y_3182_,
    );
    lean_dec(v___y_3182_);
    lean_dec_ref(v___y_3181_);
    lean_dec(v___y_3180_);
    lean_dec_ref(v___y_3179_);
    return v_res_3186_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(
    mut v_msgData_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
    mut v___y_3191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193_ = lean_st_ref_get(v___y_3191_);
    v_env_3194_ = lean_ctor_get(v___x_3193_, 0);
    lean_inc_ref(v_env_3194_);
    lean_dec(v___x_3193_);
    v___x_3195_ = lean_st_ref_get(v___y_3189_);
    v_mctx_3196_ = lean_ctor_get(v___x_3195_, 0);
    lean_inc_ref(v_mctx_3196_);
    lean_dec(v___x_3195_);
    v_lctx_3197_ = lean_ctor_get(v___y_3188_, 2);
    v_options_3198_ = lean_ctor_get(v___y_3190_, 2);
    lean_inc_ref(v_options_3198_);
    lean_inc_ref(v_lctx_3197_);
    v___x_3199_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3199_, 0, v_env_3194_);
    lean_ctor_set(v___x_3199_, 1, v_mctx_3196_);
    lean_ctor_set(v___x_3199_, 2, v_lctx_3197_);
    lean_ctor_set(v___x_3199_, 3, v_options_3198_);
    v___x_3200_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3200_, 0, v___x_3199_);
    lean_ctor_set(v___x_3200_, 1, v_msgData_3187_);
    v___x_3201_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3201_, 0, v___x_3200_);
    return v___x_3201_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(
    mut v_msgData_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
    mut v___y_3206_: *mut LeanObject,
    mut v___y_3207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3208_: *mut LeanObject = core::ptr::null_mut();
    v_res_3208_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msgData_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
    lean_dec(v___y_3206_);
    lean_dec_ref(v___y_3205_);
    lean_dec(v___y_3204_);
    lean_dec_ref(v___y_3203_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(
    mut v_msg_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
    mut v___y_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3215_ = lean_ctor_get(v___y_3212_, 5);
                v___x_3216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
                v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
                v_isSharedCheck_3225_ = (!lean_is_exclusive(v___x_3216_)) as u8;
                if v_isSharedCheck_3225_ == 0 {
                    v___x_3219_ = v___x_3216_;
                    v_isShared_3220_ = v_isSharedCheck_3225_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3217_);
                    lean_dec(v___x_3216_);
                    v___x_3219_ = lean_box(0);
                    v_isShared_3220_ = v_isSharedCheck_3225_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3215_);
                v___x_3221_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3221_, 0, v_ref_3215_);
                lean_ctor_set(v___x_3221_, 1, v_a_3217_);
                if v_isShared_3220_ == 0 {
                    lean_ctor_set_tag(v___x_3219_, 1);
                    lean_ctor_set(v___x_3219_, 0, v___x_3221_);
                    v___x_3223_ = v___x_3219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(
    mut v_msg_3226_: *mut LeanObject,
    mut v___y_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3232_: *mut LeanObject = core::ptr::null_mut();
    v_res_3232_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(
        v_msg_3226_,
        v___y_3227_,
        v___y_3228_,
        v___y_3229_,
        v___y_3230_,
    );
    lean_dec(v___y_3230_);
    lean_dec_ref(v___y_3229_);
    lean_dec(v___y_3228_);
    lean_dec_ref(v___y_3227_);
    return v_res_3232_;
}
pub unsafe fn _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_Elab_WF_withAppN___lam__0___closed__0;
    v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
    return v___x_3235_;
}
pub unsafe fn l_Lean_Elab_WF_withAppN___lam__0(
    mut v_args_3236_: *mut LeanObject,
    mut v_k_3237_: *mut LeanObject,
    mut v___x_3238_: u8,
    mut v_missing_3239_: *mut LeanObject,
    mut v_xs_3240_: *mut LeanObject,
    mut v_x_3241_: *mut LeanObject,
    mut v___y_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3254_ = lean_array_get_size(v_xs_3240_);
                v___x_3255_ = lean_nat_dec_lt(v___x_3254_, v_missing_3239_);
                if v___x_3255_ == 0 {
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_k_3237_);
                    lean_dec_ref(v_args_3236_);
                    v___x_3256_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_withAppN___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_withAppN___lam__0___closed__1_once),
                        _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1,
                    );
                    v___x_3257_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(
                        v___x_3256_,
                        v___y_3242_,
                        v___y_3243_,
                        v___y_3244_,
                        v___y_3245_,
                    );
                    v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
                    v_isSharedCheck_3265_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                    if v_isSharedCheck_3265_ == 0 {
                        v___x_3260_ = v___x_3257_;
                        v_isShared_3261_ = v_isSharedCheck_3265_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3258_);
                        lean_dec(v___x_3257_);
                        v___x_3260_ = lean_box(0);
                        v_isShared_3261_ = v_isSharedCheck_3265_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3248_ = l_Array_append___redArg(v_args_3236_, v_xs_3240_);
                lean_inc(v___y_3245_);
                lean_inc_ref(v___y_3244_);
                lean_inc(v___y_3243_);
                lean_inc_ref(v___y_3242_);
                v___x_3249_ = lean_apply_6(
                    v_k_3237_,
                    v___x_3248_,
                    v___y_3242_,
                    v___y_3243_,
                    v___y_3244_,
                    v___y_3245_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3249_) == 0 {
                    v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
                    lean_inc(v_a_3250_);
                    lean_dec_ref_known(v___x_3249_, 1);
                    v___x_3251_ = 1;
                    v___x_3252_ = 1;
                    v___x_3253_ = l_Lean_Meta_mkLambdaFVars(
                        v_xs_3240_,
                        v_a_3250_,
                        v___x_3238_,
                        v___x_3251_,
                        v___x_3238_,
                        v___x_3251_,
                        v___x_3252_,
                        v___y_3242_,
                        v___y_3243_,
                        v___y_3244_,
                        v___y_3245_,
                    );
                    return v___x_3253_;
                } else {
                    return v___x_3249_;
                }
            }
            2 => {
                if v_isShared_3261_ == 0 {
                    v___x_3263_ = v___x_3260_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_withAppN___lam__0___boxed(
    mut v_args_3266_: *mut LeanObject,
    mut v_k_3267_: *mut LeanObject,
    mut v___x_3268_: *mut LeanObject,
    mut v_missing_3269_: *mut LeanObject,
    mut v_xs_3270_: *mut LeanObject,
    mut v_x_3271_: *mut LeanObject,
    mut v___y_3272_: *mut LeanObject,
    mut v___y_3273_: *mut LeanObject,
    mut v___y_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
    mut v___y_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2318__boxed_3277_: u8 = 0;
    let mut v_res_3278_: *mut LeanObject = core::ptr::null_mut();
    v___x_2318__boxed_3277_ = (lean_unbox(v___x_3268_) as u8);
    v_res_3278_ = l_Lean_Elab_WF_withAppN___lam__0(
        v_args_3266_,
        v_k_3267_,
        v___x_2318__boxed_3277_,
        v_missing_3269_,
        v_xs_3270_,
        v_x_3271_,
        v___y_3272_,
        v___y_3273_,
        v___y_3274_,
        v___y_3275_,
    );
    lean_dec(v___y_3275_);
    lean_dec_ref(v___y_3274_);
    lean_dec(v___y_3273_);
    lean_dec_ref(v___y_3272_);
    lean_dec_ref(v_x_3271_);
    lean_dec_ref(v_xs_3270_);
    lean_dec(v_missing_3269_);
    return v_res_3278_;
}
pub unsafe fn _init_l_Lean_Elab_WF_withAppN___closed__0() -> *mut LeanObject {
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3280_: *mut LeanObject = core::ptr::null_mut();
    v___x_3279_ = lean_box(0);
    v_dummy_3280_ = l_Lean_Expr_sort___override(v___x_3279_);
    return v_dummy_3280_;
}
pub unsafe fn l_Lean_Elab_WF_withAppN(
    mut v_n_3281_: *mut LeanObject,
    mut v_e_3282_: *mut LeanObject,
    mut v_k_3283_: *mut LeanObject,
    mut v_a_3284_: *mut LeanObject,
    mut v_a_3285_: *mut LeanObject,
    mut v_a_3286_: *mut LeanObject,
    mut v_a_3287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dummy_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: u8 = 0;
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v_missing_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3309_: u8 = 0;
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v_lower_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: u8 = 0;
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_dummy_3289_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_withAppN___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_withAppN___closed__0_once),
                    _init_l_Lean_Elab_WF_withAppN___closed__0,
                );
                v_nargs_3290_ = l_Lean_Expr_getAppNumArgs(v_e_3282_);
                lean_inc(v_nargs_3290_);
                v___x_3291_ = lean_mk_array(v_nargs_3290_, v_dummy_3289_);
                v___x_3292_ = lean_unsigned_to_nat(1);
                v___x_3293_ = lean_nat_sub(v_nargs_3290_, v___x_3292_);
                lean_dec(v_nargs_3290_);
                lean_inc_ref(v_e_3282_);
                v_args_3294_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_3282_,
                    v___x_3291_,
                    v___x_3293_,
                );
                v___x_3295_ = lean_array_get_size(v_args_3294_);
                v___x_3296_ = lean_nat_dec_le(v_n_3281_, v___x_3295_);
                if v___x_3296_ == 0 {
                    lean_inc(v_a_3287_);
                    lean_inc_ref(v_a_3286_);
                    lean_inc(v_a_3285_);
                    lean_inc_ref(v_a_3284_);
                    v___x_3297_ =
                        lean_infer_type(v_e_3282_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
                    if lean_obj_tag(v___x_3297_) == 0 {
                        v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
                        v_isSharedCheck_3309_ = (!lean_is_exclusive(v___x_3297_)) as u8;
                        if v_isSharedCheck_3309_ == 0 {
                            v___x_3300_ = v___x_3297_;
                            v_isShared_3301_ = v_isSharedCheck_3309_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3298_);
                            lean_dec(v___x_3297_);
                            v___x_3300_ = lean_box(0);
                            v_isShared_3301_ = v_isSharedCheck_3309_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_args_3294_);
                        lean_dec_ref(v_k_3283_);
                        lean_dec(v_n_3281_);
                        return v___x_3297_;
                    }
                } else {
                    lean_dec_ref(v_e_3282_);
                    v___x_3310_ = lean_unsigned_to_nat(0);
                    lean_inc(v_n_3281_);
                    lean_inc_ref(v_args_3294_);
                    v___x_3311_ = l_Array_toSubarray___redArg(v_args_3294_, v___x_3310_, v_n_3281_);
                    v___x_3312_ = l_Subarray_copy___redArg(v___x_3311_);
                    lean_inc(v_a_3287_);
                    lean_inc_ref(v_a_3286_);
                    lean_inc(v_a_3285_);
                    lean_inc_ref(v_a_3284_);
                    v___x_3313_ = lean_apply_6(
                        v_k_3283_,
                        v___x_3312_,
                        v_a_3284_,
                        v_a_3285_,
                        v_a_3286_,
                        v_a_3287_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3313_) == 0 {
                        v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
                        v_isSharedCheck_3328_ = (!lean_is_exclusive(v___x_3313_)) as u8;
                        if v_isSharedCheck_3328_ == 0 {
                            v___x_3316_ = v___x_3313_;
                            v_isShared_3317_ = v_isSharedCheck_3328_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3314_);
                            lean_dec(v___x_3313_);
                            v___x_3316_ = lean_box(0);
                            v_isShared_3317_ = v_isSharedCheck_3328_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_args_3294_);
                        lean_dec(v_n_3281_);
                        return v___x_3313_;
                    }
                }
            }
            1 => {
                v_missing_3302_ = lean_nat_sub(v_n_3281_, v___x_3295_);
                lean_dec(v_n_3281_);
                v___x_3303_ = lean_box((v___x_3296_) as usize);
                lean_inc(v_missing_3302_);
                v___f_3304_ = lean_alloc_closure(
                    l_Lean_Elab_WF_withAppN___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___f_3304_, 0, v_args_3294_);
                lean_closure_set(v___f_3304_, 1, v_k_3283_);
                lean_closure_set(v___f_3304_, 2, v___x_3303_);
                lean_closure_set(v___f_3304_, 3, v_missing_3302_);
                if v_isShared_3301_ == 0 {
                    lean_ctor_set_tag(v___x_3300_, 1);
                    lean_ctor_set(v___x_3300_, 0, v_missing_3302_);
                    v___x_3306_ = v___x_3300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_missing_3302_);
                    v___x_3306_ = v_reuseFailAlloc_3308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3307_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_a_3298_, v___x_3306_, v___f_3304_, v___x_3296_, v___x_3296_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
                return v___x_3307_;
            }
            3 => {
                v___x_3327_ = lean_nat_dec_le(v_n_3281_, v___x_3310_);
                if v___x_3327_ == 0 {
                    v_lower_3319_ = v_n_3281_;
                    v_upper_3320_ = v___x_3295_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_n_3281_);
                    v_lower_3319_ = v___x_3310_;
                    v_upper_3320_ = v___x_3295_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3321_ =
                    l_Array_toSubarray___redArg(v_args_3294_, v_lower_3319_, v_upper_3320_);
                v___x_3322_ = l_Subarray_copy___redArg(v___x_3321_);
                v___x_3323_ = l_Lean_mkAppN(v_a_3314_, v___x_3322_);
                lean_dec_ref(v___x_3322_);
                if v_isShared_3317_ == 0 {
                    lean_ctor_set(v___x_3316_, 0, v___x_3323_);
                    v___x_3325_ = v___x_3316_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
                    v___x_3325_ = v_reuseFailAlloc_3326_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_withAppN___boxed(
    mut v_n_3329_: *mut LeanObject,
    mut v_e_3330_: *mut LeanObject,
    mut v_k_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3337_: *mut LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Lean_Elab_WF_withAppN(
        v_n_3329_, v_e_3330_, v_k_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_,
    );
    lean_dec(v_a_3335_);
    lean_dec_ref(v_a_3334_);
    lean_dec(v_a_3333_);
    lean_dec_ref(v_a_3332_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(
    mut v_00_u03b1_3338_: *mut LeanObject,
    mut v_msg_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(
        v_msg_3339_,
        v___y_3340_,
        v___y_3341_,
        v___y_3342_,
        v___y_3343_,
    );
    return v___x_3345_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(
    mut v_00_u03b1_3346_: *mut LeanObject,
    mut v_msg_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3353_: *mut LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(
        v_00_u03b1_3346_,
        v_msg_3347_,
        v___y_3348_,
        v___y_3349_,
        v___y_3350_,
        v___y_3351_,
    );
    lean_dec(v___y_3351_);
    lean_dec_ref(v___y_3350_);
    lean_dec(v___y_3349_);
    lean_dec_ref(v___y_3348_);
    return v_res_3353_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_packCalls_spec__1(
    mut v_msg_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447__overap_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    v___f_3361_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0;
    v___x_1447__overap_3362_ = lean_panic_fn_borrowed(v___f_3361_, v_msg_3355_);
    lean_inc(v___y_3359_);
    lean_inc_ref(v___y_3358_);
    lean_inc(v___y_3357_);
    lean_inc_ref(v___y_3356_);
    v___x_3363_ = lean_apply_5(
        v___x_1447__overap_3362_,
        v___y_3356_,
        v___y_3357_,
        v___y_3358_,
        v___y_3359_,
        lean_box(0),
    );
    return v___x_3363_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(
    mut v_msg_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3370_: *mut LeanObject = core::ptr::null_mut();
    v_res_3370_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(
        v_msg_3364_,
        v___y_3365_,
        v___y_3366_,
        v___y_3367_,
        v___y_3368_,
    );
    lean_dec(v___y_3368_);
    lean_dec_ref(v___y_3367_);
    lean_dec(v___y_3366_);
    lean_dec_ref(v___y_3365_);
    return v_res_3370_;
}
pub unsafe fn l_Lean_Elab_WF_packCalls___lam__0(
    mut v_x_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    v___x_3379_ = l_Lean_Elab_WF_packCalls___lam__0___closed__0;
    v___x_3380_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3380_, 0, v___x_3379_);
    return v___x_3380_;
}
pub unsafe fn l_Lean_Elab_WF_packCalls___lam__0___boxed(
    mut v_x_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3387_: *mut LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_Lean_Elab_WF_packCalls___lam__0(
        v_x_3381_,
        v___y_3382_,
        v___y_3383_,
        v___y_3384_,
        v___y_3385_,
    );
    lean_dec(v___y_3385_);
    lean_dec_ref(v___y_3384_);
    lean_dec(v___y_3383_);
    lean_dec_ref(v___y_3382_);
    lean_dec_ref(v_x_3381_);
    return v_res_3387_;
}
pub unsafe fn l_Lean_Elab_WF_packCalls___lam__1(
    mut v___x_3388_: *mut LeanObject,
    mut v_argsPacker_3389_: *mut LeanObject,
    mut v___x_3390_: *mut LeanObject,
    mut v_val_3391_: *mut LeanObject,
    mut v_newF_3392_: *mut LeanObject,
    mut v_args_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3404_: u8 = 0;
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3399_ =
                    l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_3388_, v_args_3393_);
                v___x_3400_ = l_Lean_Meta_ArgsPacker_pack(
                    v_argsPacker_3389_,
                    v___x_3390_,
                    v_val_3391_,
                    v___x_3399_,
                    v___y_3394_,
                    v___y_3395_,
                    v___y_3396_,
                    v___y_3397_,
                );
                lean_dec_ref(v___x_3399_);
                if lean_obj_tag(v___x_3400_) == 0 {
                    v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
                    v_isSharedCheck_3409_ = (!lean_is_exclusive(v___x_3400_)) as u8;
                    if v_isSharedCheck_3409_ == 0 {
                        v___x_3403_ = v___x_3400_;
                        v_isShared_3404_ = v_isSharedCheck_3409_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3401_);
                        lean_dec(v___x_3400_);
                        v___x_3403_ = lean_box(0);
                        v_isShared_3404_ = v_isSharedCheck_3409_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newF_3392_);
                    return v___x_3400_;
                }
            }
            1 => {
                v___x_3405_ = l_Lean_Expr_app___override(v_newF_3392_, v_a_3401_);
                if v_isShared_3404_ == 0 {
                    lean_ctor_set(v___x_3403_, 0, v___x_3405_);
                    v___x_3407_ = v___x_3403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
                    v___x_3407_ = v_reuseFailAlloc_3408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3407_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_packCalls___lam__1___boxed(
    mut v___x_3410_: *mut LeanObject,
    mut v_argsPacker_3411_: *mut LeanObject,
    mut v___x_3412_: *mut LeanObject,
    mut v_val_3413_: *mut LeanObject,
    mut v_newF_3414_: *mut LeanObject,
    mut v_args_3415_: *mut LeanObject,
    mut v___y_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3421_: *mut LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_Lean_Elab_WF_packCalls___lam__1(
        v___x_3410_,
        v_argsPacker_3411_,
        v___x_3412_,
        v_val_3413_,
        v_newF_3414_,
        v_args_3415_,
        v___y_3416_,
        v___y_3417_,
        v___y_3418_,
        v___y_3419_,
    );
    lean_dec(v___y_3419_);
    lean_dec_ref(v___y_3418_);
    lean_dec(v___y_3417_);
    lean_dec_ref(v___y_3416_);
    lean_dec_ref(v_args_3415_);
    lean_dec_ref(v_argsPacker_3411_);
    lean_dec_ref(v___x_3410_);
    return v_res_3421_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(
    mut v_xs_3422_: *mut LeanObject,
    mut v_v_3423_: *mut LeanObject,
    mut v_i_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3425_ = lean_array_get_size(v_xs_3422_);
                v___x_3426_ = lean_nat_dec_lt(v_i_3424_, v___x_3425_);
                if v___x_3426_ == 0 {
                    lean_dec(v_i_3424_);
                    v___x_3427_ = lean_box(0);
                    return v___x_3427_;
                } else {
                    v___x_3428_ = lean_array_fget_borrowed(v_xs_3422_, v_i_3424_);
                    v___x_3429_ = lean_name_eq(v___x_3428_, v_v_3423_);
                    if v___x_3429_ == 0 {
                        v___x_3430_ = lean_unsigned_to_nat(1);
                        v___x_3431_ = lean_nat_add(v_i_3424_, v___x_3430_);
                        lean_dec(v_i_3424_);
                        v_i_3424_ = v___x_3431_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3433_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3433_, 0, v_i_3424_);
                        return v___x_3433_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(
    mut v_xs_3434_: *mut LeanObject,
    mut v_v_3435_: *mut LeanObject,
    mut v_i_3436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3437_: *mut LeanObject = core::ptr::null_mut();
    v_res_3437_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_3434_, v_v_3435_, v_i_3436_);
    lean_dec(v_v_3435_);
    lean_dec_ref(v_xs_3434_);
    return v_res_3437_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(
    mut v_xs_3438_: *mut LeanObject,
    mut v_v_3439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    v___x_3440_ = lean_unsigned_to_nat(0);
    v___x_3441_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_3438_, v_v_3439_, v___x_3440_);
    return v___x_3441_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(
    mut v_xs_3442_: *mut LeanObject,
    mut v_v_3443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3444_: *mut LeanObject = core::ptr::null_mut();
    v_res_3444_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_3442_, v_v_3443_);
    lean_dec(v_v_3443_);
    lean_dec_ref(v_xs_3442_);
    return v_res_3444_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(
    mut v_xs_3445_: *mut LeanObject,
    mut v_v_3446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3447_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_3445_, v_v_3446_);
                if lean_obj_tag(v___x_3447_) == 0 {
                    v___x_3448_ = lean_box(0);
                    return v___x_3448_;
                } else {
                    v_val_3449_ = lean_ctor_get(v___x_3447_, 0);
                    v_isSharedCheck_3456_ = (!lean_is_exclusive(v___x_3447_)) as u8;
                    if v_isSharedCheck_3456_ == 0 {
                        v___x_3451_ = v___x_3447_;
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3449_);
                        lean_dec(v___x_3447_);
                        v___x_3451_ = lean_box(0);
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3452_ == 0 {
                    v___x_3454_ = v___x_3451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_val_3449_);
                    v___x_3454_ = v_reuseFailAlloc_3455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(
    mut v_xs_3457_: *mut LeanObject,
    mut v_v_3458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3459_: *mut LeanObject = core::ptr::null_mut();
    v_res_3459_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_xs_3457_, v_v_3458_);
    lean_dec(v_v_3458_);
    lean_dec_ref(v_xs_3457_);
    return v_res_3459_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(
    mut v___x_3460_: u8,
    mut v_sz_3461_: usize,
    mut v_i_3462_: usize,
    mut v_bs_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3464_: u8 = 0;
    let mut v_v_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3469_: u8 = 0;
    let mut v___x_3470_: usize = 0;
    let mut v___x_3471_: usize = 0;
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3464_ = lean_usize_dec_lt(v_i_3462_, v_sz_3461_);
                if v___x_3464_ == 0 {
                    return v_bs_3463_;
                } else {
                    v_v_3465_ = lean_array_uget(v_bs_3463_, v_i_3462_);
                    v___x_3466_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3467_ = lean_array_uset(v_bs_3463_, v_i_3462_, v___x_3466_);
                    if lean_obj_tag(v_v_3465_) == 0 {
                        v___x_3475_ = 0;
                        v___y_3469_ = v___x_3475_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v_v_3465_, 1);
                        v___y_3469_ = v___x_3460_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3470_ = 1usize;
                v___x_3471_ = lean_usize_add(v_i_3462_, v___x_3470_);
                v___x_3472_ = lean_box((v___y_3469_) as usize);
                v___x_3473_ = lean_array_uset(v_bs_x27_3467_, v_i_3462_, v___x_3472_);
                v_i_3462_ = v___x_3471_;
                v_bs_3463_ = v___x_3473_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(
    mut v___x_3476_: *mut LeanObject,
    mut v_sz_3477_: *mut LeanObject,
    mut v_i_3478_: *mut LeanObject,
    mut v_bs_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9900__boxed_3480_: u8 = 0;
    let mut v_sz_boxed_3481_: usize = 0;
    let mut v_i_boxed_3482_: usize = 0;
    let mut v_res_3483_: *mut LeanObject = core::ptr::null_mut();
    v___x_9900__boxed_3480_ = (lean_unbox(v___x_3476_) as u8);
    v_sz_boxed_3481_ = lean_unbox_usize(v_sz_3477_);
    lean_dec(v_sz_3477_);
    v_i_boxed_3482_ = lean_unbox_usize(v_i_3478_);
    lean_dec(v_i_3478_);
    v_res_3483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_9900__boxed_3480_, v_sz_boxed_3481_, v_i_boxed_3482_, v_bs_3479_);
    return v_res_3483_;
}
pub unsafe fn _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3() -> *mut LeanObject {
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_Elab_WF_packCalls___lam__2___closed__2;
    v___x_3488_ = lean_unsigned_to_nat(6);
    v___x_3489_ = lean_unsigned_to_nat(55);
    v___x_3490_ = l_Lean_Elab_WF_packCalls___lam__2___closed__1;
    v___x_3491_ = l_Lean_Elab_WF_packCalls___lam__2___closed__0;
    v___x_3492_ = l_mkPanicMessageWithDecl(
        v___x_3491_,
        v___x_3490_,
        v___x_3489_,
        v___x_3488_,
        v___x_3487_,
    );
    return v___x_3492_;
}
pub unsafe fn _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4() -> *mut LeanObject {
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    v___x_3493_ = l_Array_instInhabited(lean_box(0));
    return v___x_3493_;
}
pub unsafe fn l_Lean_Elab_WF_packCalls___lam__2(
    mut v_funNames_3494_: *mut LeanObject,
    mut v_fixedParamPerms_3495_: *mut LeanObject,
    mut v_argsPacker_3496_: *mut LeanObject,
    mut v___x_3497_: *mut LeanObject,
    mut v_newF_3498_: *mut LeanObject,
    mut v_e_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v_perms_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3523_: usize = 0;
    let mut v___x_3524_: usize = 0;
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3538_: u8 = 0;
    let mut v_a_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3542_: u8 = 0;
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3546_: u8 = 0;
    let mut v_isSharedCheck_3547_: u8 = 0;
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = l_Lean_Expr_getAppFn(v_e_3499_);
                v___x_3506_ = l_Lean_Expr_isConst(v___x_3505_);
                if v___x_3506_ == 0 {
                    lean_dec_ref(v___x_3505_);
                    lean_dec_ref(v_newF_3498_);
                    lean_dec_ref(v___x_3497_);
                    lean_dec_ref(v_argsPacker_3496_);
                    v___x_3507_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3507_, 0, v_e_3499_);
                    v___x_3508_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3508_, 0, v___x_3507_);
                    return v___x_3508_;
                } else {
                    v___x_3509_ = l_Lean_Expr_constName_x21(v___x_3505_);
                    lean_dec_ref(v___x_3505_);
                    v___x_3510_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(
                        v_funNames_3494_,
                        v___x_3509_,
                    );
                    lean_dec(v___x_3509_);
                    if lean_obj_tag(v___x_3510_) == 1 {
                        v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
                        v_isSharedCheck_3547_ = (!lean_is_exclusive(v___x_3510_)) as u8;
                        if v_isSharedCheck_3547_ == 0 {
                            v___x_3513_ = v___x_3510_;
                            v_isShared_3514_ = v_isSharedCheck_3547_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_3511_);
                            lean_dec(v___x_3510_);
                            v___x_3513_ = lean_box(0);
                            v_isShared_3514_ = v_isSharedCheck_3547_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3510_);
                        lean_dec_ref(v_newF_3498_);
                        lean_dec_ref(v___x_3497_);
                        lean_dec_ref(v_argsPacker_3496_);
                        v___x_3548_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3548_, 0, v_e_3499_);
                        v___x_3549_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3549_, 0, v___x_3548_);
                        return v___x_3549_;
                    }
                }
            }
            1 => {
                v_perms_3515_ = lean_ctor_get(v_fixedParamPerms_3495_, 1);
                v___x_3516_ = lean_array_get_size(v_perms_3515_);
                v___x_3517_ = lean_nat_dec_lt(v_val_3511_, v___x_3516_);
                if v___x_3517_ == 0 {
                    lean_del_object(v___x_3513_);
                    lean_dec(v_val_3511_);
                    lean_dec_ref(v_e_3499_);
                    lean_dec_ref(v_newF_3498_);
                    lean_dec_ref(v___x_3497_);
                    lean_dec_ref(v_argsPacker_3496_);
                    v___x_3518_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__3_once),
                        _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3,
                    );
                    v___x_3519_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(
                        v___x_3518_,
                        v___y_3500_,
                        v___y_3501_,
                        v___y_3502_,
                        v___y_3503_,
                    );
                    return v___x_3519_;
                } else {
                    v___x_3520_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4_once),
                        _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4,
                    );
                    v___x_3521_ = lean_array_get_borrowed(v___x_3520_, v_perms_3515_, v_val_3511_);
                    lean_inc_n(v___x_3521_, 2);
                    v___f_3522_ = lean_alloc_closure(
                        l_Lean_Elab_WF_packCalls___lam__1___boxed as *mut core::ffi::c_void,
                        11,
                        5,
                    );
                    lean_closure_set(v___f_3522_, 0, v___x_3521_);
                    lean_closure_set(v___f_3522_, 1, v_argsPacker_3496_);
                    lean_closure_set(v___f_3522_, 2, v___x_3497_);
                    lean_closure_set(v___f_3522_, 3, v_val_3511_);
                    lean_closure_set(v___f_3522_, 4, v_newF_3498_);
                    v_sz_3523_ = lean_array_size(v___x_3521_);
                    v___x_3524_ = 0usize;
                    v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_3506_, v_sz_3523_, v___x_3524_, v___x_3521_);
                    v___x_3526_ = lean_array_get_size(v___x_3525_);
                    lean_dec_ref(v___x_3525_);
                    v___x_3527_ = l_Lean_Elab_WF_withAppN(
                        v___x_3526_,
                        v_e_3499_,
                        v___f_3522_,
                        v___y_3500_,
                        v___y_3501_,
                        v___y_3502_,
                        v___y_3503_,
                    );
                    if lean_obj_tag(v___x_3527_) == 0 {
                        v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
                        v_isSharedCheck_3538_ = (!lean_is_exclusive(v___x_3527_)) as u8;
                        if v_isSharedCheck_3538_ == 0 {
                            v___x_3530_ = v___x_3527_;
                            v_isShared_3531_ = v_isSharedCheck_3538_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3528_);
                            lean_dec(v___x_3527_);
                            v___x_3530_ = lean_box(0);
                            v_isShared_3531_ = v_isSharedCheck_3538_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3513_);
                        v_a_3539_ = lean_ctor_get(v___x_3527_, 0);
                        v_isSharedCheck_3546_ = (!lean_is_exclusive(v___x_3527_)) as u8;
                        if v_isSharedCheck_3546_ == 0 {
                            v___x_3541_ = v___x_3527_;
                            v_isShared_3542_ = v_isSharedCheck_3546_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3539_);
                            lean_dec(v___x_3527_);
                            v___x_3541_ = lean_box(0);
                            v_isShared_3542_ = v_isSharedCheck_3546_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_3514_ == 0 {
                    lean_ctor_set_tag(v___x_3513_, 0);
                    lean_ctor_set(v___x_3513_, 0, v_a_3528_);
                    v___x_3533_ = v___x_3513_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3528_);
                    v___x_3533_ = v_reuseFailAlloc_3537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3531_ == 0 {
                    lean_ctor_set(v___x_3530_, 0, v___x_3533_);
                    v___x_3535_ = v___x_3530_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
                    v___x_3535_ = v_reuseFailAlloc_3536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3535_;
            }
            5 => {
                if v_isShared_3542_ == 0 {
                    v___x_3544_ = v___x_3541_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
                    v___x_3544_ = v_reuseFailAlloc_3545_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_packCalls___lam__2___boxed(
    mut v_funNames_3550_: *mut LeanObject,
    mut v_fixedParamPerms_3551_: *mut LeanObject,
    mut v_argsPacker_3552_: *mut LeanObject,
    mut v___x_3553_: *mut LeanObject,
    mut v_newF_3554_: *mut LeanObject,
    mut v_e_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
    mut v___y_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3561_: *mut LeanObject = core::ptr::null_mut();
    v_res_3561_ = l_Lean_Elab_WF_packCalls___lam__2(
        v_funNames_3550_,
        v_fixedParamPerms_3551_,
        v_argsPacker_3552_,
        v___x_3553_,
        v_newF_3554_,
        v_e_3555_,
        v___y_3556_,
        v___y_3557_,
        v___y_3558_,
        v___y_3559_,
    );
    lean_dec(v___y_3559_);
    lean_dec_ref(v___y_3558_);
    lean_dec(v___y_3557_);
    lean_dec_ref(v___y_3556_);
    lean_dec_ref(v_fixedParamPerms_3551_);
    lean_dec_ref(v_funNames_3550_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(
    mut v_00_u03b1_3562_: *mut LeanObject,
    mut v_x_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    v___x_3569_ = lean_apply_1(v_x_3563_, lean_box(0));
    v___x_3570_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3570_, 0, v___x_3569_);
    return v___x_3570_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(
    mut v_00_u03b1_3571_: *mut LeanObject,
    mut v_x_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
    mut v___y_3575_: *mut LeanObject,
    mut v___y_3576_: *mut LeanObject,
    mut v___y_3577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3578_: *mut LeanObject = core::ptr::null_mut();
    v_res_3578_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(
        v_00_u03b1_3571_,
        v_x_3572_,
        v___y_3573_,
        v___y_3574_,
        v___y_3575_,
        v___y_3576_,
    );
    lean_dec(v___y_3576_);
    lean_dec_ref(v___y_3575_);
    lean_dec(v___y_3574_);
    lean_dec_ref(v___y_3573_);
    return v_res_3578_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    v___x_3584_ = l_Lean_maxRecDepthErrorMessage;
    v___x_3585_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3585_, 0, v___x_3584_);
    return v___x_3585_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    v___x_3586_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3);
    v___x_3587_ = l_Lean_MessageData_ofFormat(v___x_3586_);
    return v___x_3587_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    v___x_3588_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4);
    v___x_3589_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2;
    v___x_3590_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_3590_, 0, v___x_3589_);
    lean_ctor_set(v___x_3590_, 1, v___x_3588_);
    return v___x_3590_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(
    mut v_ref_3591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    v___x_3593_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5);
    v___x_3594_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3594_, 0, v_ref_3591_);
    lean_ctor_set(v___x_3594_, 1, v___x_3593_);
    v___x_3595_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3595_, 0, v___x_3594_);
    return v___x_3595_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(
    mut v_ref_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3598_: *mut LeanObject = core::ptr::null_mut();
    v_res_3598_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_3596_);
    return v_res_3598_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(
    mut v_x_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
    mut v___y_3603_: *mut LeanObject,
    mut v___y_3604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3611_: u8 = 0;
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3615_: u8 = 0;
    let mut v_fileName_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3628_: u8 = 0;
    let mut v_cancelTk_x3f_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3630_: u8 = 0;
    let mut v_inheritedTraceOptions_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3616_ = lean_ctor_get(v___y_3603_, 0);
                v_fileMap_3617_ = lean_ctor_get(v___y_3603_, 1);
                v_options_3618_ = lean_ctor_get(v___y_3603_, 2);
                v_currRecDepth_3619_ = lean_ctor_get(v___y_3603_, 3);
                v_maxRecDepth_3620_ = lean_ctor_get(v___y_3603_, 4);
                v_ref_3621_ = lean_ctor_get(v___y_3603_, 5);
                v_currNamespace_3622_ = lean_ctor_get(v___y_3603_, 6);
                v_openDecls_3623_ = lean_ctor_get(v___y_3603_, 7);
                v_initHeartbeats_3624_ = lean_ctor_get(v___y_3603_, 8);
                v_maxHeartbeats_3625_ = lean_ctor_get(v___y_3603_, 9);
                v_quotContext_3626_ = lean_ctor_get(v___y_3603_, 10);
                v_currMacroScope_3627_ = lean_ctor_get(v___y_3603_, 11);
                v_diag_3628_ = lean_ctor_get_uint8(
                    v___y_3603_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3629_ = lean_ctor_get(v___y_3603_, 12);
                v_suppressElabErrors_3630_ = lean_ctor_get_uint8(
                    v___y_3603_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3631_ = lean_ctor_get(v___y_3603_, 13);
                v___x_3637_ = lean_unsigned_to_nat(0);
                v___x_3638_ = lean_nat_dec_eq(v_maxRecDepth_3620_, v___x_3637_);
                if v___x_3638_ == 0 {
                    v___x_3639_ = lean_nat_dec_eq(v_currRecDepth_3619_, v_maxRecDepth_3620_);
                    if v___x_3639_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        lean_dec_ref(v_x_3599_);
                        lean_inc(v_ref_3621_);
                        v___x_3640_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_3621_);
                        v___y_3607_ = v___x_3640_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_3607_) == 0 {
                    return v___y_3607_;
                } else {
                    v_a_3608_ = lean_ctor_get(v___y_3607_, 0);
                    v_isSharedCheck_3615_ = (!lean_is_exclusive(v___y_3607_)) as u8;
                    if v_isSharedCheck_3615_ == 0 {
                        v___x_3610_ = v___y_3607_;
                        v_isShared_3611_ = v_isSharedCheck_3615_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3608_);
                        lean_dec(v___y_3607_);
                        v___x_3610_ = lean_box(0);
                        v_isShared_3611_ = v_isSharedCheck_3615_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3611_ == 0 {
                    v___x_3613_ = v___x_3610_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
                    v___x_3613_ = v_reuseFailAlloc_3614_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3613_;
            }
            4 => {
                v___x_3633_ = lean_unsigned_to_nat(1);
                v___x_3634_ = lean_nat_add(v_currRecDepth_3619_, v___x_3633_);
                lean_inc_ref(v_inheritedTraceOptions_3631_);
                lean_inc(v_cancelTk_x3f_3629_);
                lean_inc(v_currMacroScope_3627_);
                lean_inc(v_quotContext_3626_);
                lean_inc(v_maxHeartbeats_3625_);
                lean_inc(v_initHeartbeats_3624_);
                lean_inc(v_openDecls_3623_);
                lean_inc(v_currNamespace_3622_);
                lean_inc(v_ref_3621_);
                lean_inc(v_maxRecDepth_3620_);
                lean_inc_ref(v_options_3618_);
                lean_inc_ref(v_fileMap_3617_);
                lean_inc_ref(v_fileName_3616_);
                v___x_3635_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3635_, 0, v_fileName_3616_);
                lean_ctor_set(v___x_3635_, 1, v_fileMap_3617_);
                lean_ctor_set(v___x_3635_, 2, v_options_3618_);
                lean_ctor_set(v___x_3635_, 3, v___x_3634_);
                lean_ctor_set(v___x_3635_, 4, v_maxRecDepth_3620_);
                lean_ctor_set(v___x_3635_, 5, v_ref_3621_);
                lean_ctor_set(v___x_3635_, 6, v_currNamespace_3622_);
                lean_ctor_set(v___x_3635_, 7, v_openDecls_3623_);
                lean_ctor_set(v___x_3635_, 8, v_initHeartbeats_3624_);
                lean_ctor_set(v___x_3635_, 9, v_maxHeartbeats_3625_);
                lean_ctor_set(v___x_3635_, 10, v_quotContext_3626_);
                lean_ctor_set(v___x_3635_, 11, v_currMacroScope_3627_);
                lean_ctor_set(v___x_3635_, 12, v_cancelTk_x3f_3629_);
                lean_ctor_set(v___x_3635_, 13, v_inheritedTraceOptions_3631_);
                lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_3628_,
                );
                lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3630_,
                );
                lean_inc(v___y_3604_);
                lean_inc(v___y_3602_);
                lean_inc_ref(v___y_3601_);
                lean_inc(v___y_3600_);
                v___x_3636_ = lean_apply_6(
                    v_x_3599_,
                    v___y_3600_,
                    v___y_3601_,
                    v___y_3602_,
                    v___x_3635_,
                    v___y_3604_,
                    lean_box(0),
                );
                v___y_3607_ = v___x_3636_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(
    mut v_x_3641_: *mut LeanObject,
    mut v___y_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3648_: *mut LeanObject = core::ptr::null_mut();
    v_res_3648_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
    lean_dec(v___y_3646_);
    lean_dec_ref(v___y_3645_);
    lean_dec(v___y_3644_);
    lean_dec_ref(v___y_3643_);
    lean_dec(v___y_3642_);
    return v_res_3648_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(
    mut v___x_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
    mut v___y_3652_: *mut LeanObject,
    mut v___y_3653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    v___x_3655_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3655_, 0, v___x_3649_);
    return v___x_3655_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(
    mut v___x_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3662_: *mut LeanObject = core::ptr::null_mut();
    v_res_3662_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
    lean_dec(v___y_3660_);
    lean_dec_ref(v___y_3659_);
    lean_dec(v___y_3658_);
    lean_dec_ref(v___y_3657_);
    return v_res_3662_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(
    mut v_k_3663_: *mut LeanObject,
    mut v___y_3664_: *mut LeanObject,
    mut v_b_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3669_);
    lean_inc_ref(v___y_3668_);
    lean_inc(v___y_3667_);
    lean_inc_ref(v___y_3666_);
    lean_inc(v___y_3664_);
    v___x_3671_ = lean_apply_7(
        v_k_3663_,
        v_b_3665_,
        v___y_3664_,
        v___y_3666_,
        v___y_3667_,
        v___y_3668_,
        v___y_3669_,
        lean_box(0),
    );
    return v___x_3671_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(
    mut v_k_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
    mut v_b_3674_: *mut LeanObject,
    mut v___y_3675_: *mut LeanObject,
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3680_: *mut LeanObject = core::ptr::null_mut();
    v_res_3680_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_3672_, v___y_3673_, v_b_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
    lean_dec(v___y_3678_);
    lean_dec_ref(v___y_3677_);
    lean_dec(v___y_3676_);
    lean_dec_ref(v___y_3675_);
    lean_dec(v___y_3673_);
    return v_res_3680_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(
    mut v_name_3681_: *mut LeanObject,
    mut v_type_3682_: *mut LeanObject,
    mut v_val_3683_: *mut LeanObject,
    mut v_k_3684_: *mut LeanObject,
    mut v_nondep_3685_: u8,
    mut v_kind_3686_: u8,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3687_);
                v___f_3693_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                lean_closure_set(v___f_3693_, 0, v_k_3684_);
                lean_closure_set(v___f_3693_, 1, v___y_3687_);
                v___x_3694_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
                    v_name_3681_,
                    v_type_3682_,
                    v_val_3683_,
                    v___f_3693_,
                    v_nondep_3685_,
                    v_kind_3686_,
                    v___y_3688_,
                    v___y_3689_,
                    v___y_3690_,
                    v___y_3691_,
                );
                if lean_obj_tag(v___x_3694_) == 0 {
                    return v___x_3694_;
                } else {
                    v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
                    v_isSharedCheck_3702_ = (!lean_is_exclusive(v___x_3694_)) as u8;
                    if v_isSharedCheck_3702_ == 0 {
                        v___x_3697_ = v___x_3694_;
                        v_isShared_3698_ = v_isSharedCheck_3702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3695_);
                        lean_dec(v___x_3694_);
                        v___x_3697_ = lean_box(0);
                        v_isShared_3698_ = v_isSharedCheck_3702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3698_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(
    mut v_name_3703_: *mut LeanObject,
    mut v_type_3704_: *mut LeanObject,
    mut v_val_3705_: *mut LeanObject,
    mut v_k_3706_: *mut LeanObject,
    mut v_nondep_3707_: *mut LeanObject,
    mut v_kind_3708_: *mut LeanObject,
    mut v___y_3709_: *mut LeanObject,
    mut v___y_3710_: *mut LeanObject,
    mut v___y_3711_: *mut LeanObject,
    mut v___y_3712_: *mut LeanObject,
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_3715_: u8 = 0;
    let mut v_kind_boxed_3716_: u8 = 0;
    let mut v_res_3717_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3715_ = (lean_unbox(v_nondep_3707_) as u8);
    v_kind_boxed_3716_ = (lean_unbox(v_kind_3708_) as u8);
    v_res_3717_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_3703_, v_type_3704_, v_val_3705_, v_k_3706_, v_nondep_boxed_3715_, v_kind_boxed_3716_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
    lean_dec(v___y_3713_);
    lean_dec_ref(v___y_3712_);
    lean_dec(v___y_3711_);
    lean_dec_ref(v___y_3710_);
    lean_dec(v___y_3709_);
    return v_res_3717_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(
    mut v_name_3718_: *mut LeanObject,
    mut v_bi_3719_: u8,
    mut v_type_3720_: *mut LeanObject,
    mut v_k_3721_: *mut LeanObject,
    mut v_kind_3722_: u8,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
    mut v___y_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3734_: u8 = 0;
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3723_);
                v___f_3729_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                lean_closure_set(v___f_3729_, 0, v_k_3721_);
                lean_closure_set(v___f_3729_, 1, v___y_3723_);
                v___x_3730_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_3718_,
                    v_bi_3719_,
                    v_type_3720_,
                    v___f_3729_,
                    v_kind_3722_,
                    v___y_3724_,
                    v___y_3725_,
                    v___y_3726_,
                    v___y_3727_,
                );
                if lean_obj_tag(v___x_3730_) == 0 {
                    return v___x_3730_;
                } else {
                    v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
                    v_isSharedCheck_3738_ = (!lean_is_exclusive(v___x_3730_)) as u8;
                    if v_isSharedCheck_3738_ == 0 {
                        v___x_3733_ = v___x_3730_;
                        v_isShared_3734_ = v_isSharedCheck_3738_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3731_);
                        lean_dec(v___x_3730_);
                        v___x_3733_ = lean_box(0);
                        v_isShared_3734_ = v_isSharedCheck_3738_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3734_ == 0 {
                    v___x_3736_ = v___x_3733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
                    v___x_3736_ = v_reuseFailAlloc_3737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(
    mut v_name_3739_: *mut LeanObject,
    mut v_bi_3740_: *mut LeanObject,
    mut v_type_3741_: *mut LeanObject,
    mut v_k_3742_: *mut LeanObject,
    mut v_kind_3743_: *mut LeanObject,
    mut v___y_3744_: *mut LeanObject,
    mut v___y_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
    mut v___y_3748_: *mut LeanObject,
    mut v___y_3749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3750_: u8 = 0;
    let mut v_kind_boxed_3751_: u8 = 0;
    let mut v_res_3752_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3750_ = (lean_unbox(v_bi_3740_) as u8);
    v_kind_boxed_3751_ = (lean_unbox(v_kind_3743_) as u8);
    v_res_3752_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_3739_, v_bi_boxed_3750_, v_type_3741_, v_k_3742_, v_kind_boxed_3751_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
    lean_dec(v___y_3748_);
    lean_dec_ref(v___y_3747_);
    lean_dec(v___y_3746_);
    lean_dec_ref(v___y_3745_);
    lean_dec(v___y_3744_);
    return v_res_3752_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(
    mut v_00_u03b1_3753_: *mut LeanObject,
    mut v_x_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    v___x_3760_ = lean_apply_1(v_x_3754_, lean_box(0));
    v___x_3761_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3761_, 0, v___x_3760_);
    return v___x_3761_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(
    mut v_00_u03b1_3762_: *mut LeanObject,
    mut v_x_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3769_: *mut LeanObject = core::ptr::null_mut();
    v_res_3769_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_3762_, v_x_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
    lean_dec(v___y_3767_);
    lean_dec_ref(v___y_3766_);
    lean_dec(v___y_3765_);
    lean_dec_ref(v___y_3764_);
    return v_res_3769_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(
    mut v_a_3770_: *mut LeanObject,
    mut v_x_3771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3771_) == 0 {
                    v___x_3772_ = lean_box(0);
                    return v___x_3772_;
                } else {
                    v_key_3773_ = lean_ctor_get(v_x_3771_, 0);
                    v_value_3774_ = lean_ctor_get(v_x_3771_, 1);
                    v_tail_3775_ = lean_ctor_get(v_x_3771_, 2);
                    v___x_3776_ = l_Lean_ExprStructEq_beq(v_key_3773_, v_a_3770_);
                    if v___x_3776_ == 0 {
                        v_x_3771_ = v_tail_3775_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3774_);
                        v___x_3778_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3778_, 0, v_value_3774_);
                        return v___x_3778_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(
    mut v_a_3779_: *mut LeanObject,
    mut v_x_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3781_: *mut LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_3779_, v_x_3780_);
    lean_dec(v_x_3780_);
    lean_dec_ref(v_a_3779_);
    return v_res_3781_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(
    mut v_m_3782_: *mut LeanObject,
    mut v_a_3783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u64 = 0;
    let mut v___x_3787_: u64 = 0;
    let mut v___x_3788_: u64 = 0;
    let mut v_fold_3789_: u64 = 0;
    let mut v___x_3790_: u64 = 0;
    let mut v___x_3791_: u64 = 0;
    let mut v___x_3792_: u64 = 0;
    let mut v___x_3793_: usize = 0;
    let mut v___x_3794_: usize = 0;
    let mut v___x_3795_: usize = 0;
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_3784_ = lean_ctor_get(v_m_3782_, 1);
    v___x_3785_ = lean_array_get_size(v_buckets_3784_);
    v___x_3786_ = l_Lean_ExprStructEq_hash(v_a_3783_);
    v___x_3787_ = 32u64;
    v___x_3788_ = lean_uint64_shift_right(v___x_3786_, v___x_3787_);
    v_fold_3789_ = lean_uint64_xor(v___x_3786_, v___x_3788_);
    v___x_3790_ = 16u64;
    v___x_3791_ = lean_uint64_shift_right(v_fold_3789_, v___x_3790_);
    v___x_3792_ = lean_uint64_xor(v_fold_3789_, v___x_3791_);
    v___x_3793_ = lean_uint64_to_usize(v___x_3792_);
    v___x_3794_ = lean_usize_of_nat(v___x_3785_);
    v___x_3795_ = 1usize;
    v___x_3796_ = lean_usize_sub(v___x_3794_, v___x_3795_);
    v___x_3797_ = lean_usize_land(v___x_3793_, v___x_3796_);
    v___x_3798_ = lean_array_uget_borrowed(v_buckets_3784_, v___x_3797_);
    v___x_3799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_3783_, v___x_3798_);
    return v___x_3799_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(
    mut v_m_3800_: *mut LeanObject,
    mut v_a_3801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3802_: *mut LeanObject = core::ptr::null_mut();
    v_res_3802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_3800_, v_a_3801_);
    lean_dec_ref(v_a_3801_);
    lean_dec_ref(v_m_3800_);
    return v_res_3802_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(
    mut v_a_3803_: *mut LeanObject,
    mut v_x_3804_: *mut LeanObject,
) -> u8 {
    let mut v___x_3805_: u8 = 0;
    let mut v_key_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3804_) == 0 {
                    v___x_3805_ = 0;
                    return v___x_3805_;
                } else {
                    v_key_3806_ = lean_ctor_get(v_x_3804_, 0);
                    v_tail_3807_ = lean_ctor_get(v_x_3804_, 2);
                    v___x_3808_ = l_Lean_ExprStructEq_beq(v_key_3806_, v_a_3803_);
                    if v___x_3808_ == 0 {
                        v_x_3804_ = v_tail_3807_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3808_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(
    mut v_a_3810_: *mut LeanObject,
    mut v_x_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3812_: u8 = 0;
    let mut v_r_3813_: *mut LeanObject = core::ptr::null_mut();
    v_res_3812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_3810_, v_x_3811_);
    lean_dec(v_x_3811_);
    lean_dec_ref(v_a_3810_);
    v_r_3813_ = lean_box((v_res_3812_) as usize);
    return v_r_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(
    mut v_x_3814_: *mut LeanObject,
    mut v_x_3815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u64 = 0;
    let mut v___x_3824_: u64 = 0;
    let mut v___x_3825_: u64 = 0;
    let mut v_fold_3826_: u64 = 0;
    let mut v___x_3827_: u64 = 0;
    let mut v___x_3828_: u64 = 0;
    let mut v___x_3829_: u64 = 0;
    let mut v___x_3830_: usize = 0;
    let mut v___x_3831_: usize = 0;
    let mut v___x_3832_: usize = 0;
    let mut v___x_3833_: usize = 0;
    let mut v___x_3834_: usize = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3815_) == 0 {
                    return v_x_3814_;
                } else {
                    v_key_3816_ = lean_ctor_get(v_x_3815_, 0);
                    v_value_3817_ = lean_ctor_get(v_x_3815_, 1);
                    v_tail_3818_ = lean_ctor_get(v_x_3815_, 2);
                    v_isSharedCheck_3841_ = (!lean_is_exclusive(v_x_3815_)) as u8;
                    if v_isSharedCheck_3841_ == 0 {
                        v___x_3820_ = v_x_3815_;
                        v_isShared_3821_ = v_isSharedCheck_3841_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3818_);
                        lean_inc(v_value_3817_);
                        lean_inc(v_key_3816_);
                        lean_dec(v_x_3815_);
                        v___x_3820_ = lean_box(0);
                        v_isShared_3821_ = v_isSharedCheck_3841_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3822_ = lean_array_get_size(v_x_3814_);
                v___x_3823_ = l_Lean_ExprStructEq_hash(v_key_3816_);
                v___x_3824_ = 32u64;
                v___x_3825_ = lean_uint64_shift_right(v___x_3823_, v___x_3824_);
                v_fold_3826_ = lean_uint64_xor(v___x_3823_, v___x_3825_);
                v___x_3827_ = 16u64;
                v___x_3828_ = lean_uint64_shift_right(v_fold_3826_, v___x_3827_);
                v___x_3829_ = lean_uint64_xor(v_fold_3826_, v___x_3828_);
                v___x_3830_ = lean_uint64_to_usize(v___x_3829_);
                v___x_3831_ = lean_usize_of_nat(v___x_3822_);
                v___x_3832_ = 1usize;
                v___x_3833_ = lean_usize_sub(v___x_3831_, v___x_3832_);
                v___x_3834_ = lean_usize_land(v___x_3830_, v___x_3833_);
                v___x_3835_ = lean_array_uget_borrowed(v_x_3814_, v___x_3834_);
                lean_inc(v___x_3835_);
                if v_isShared_3821_ == 0 {
                    lean_ctor_set(v___x_3820_, 2, v___x_3835_);
                    v___x_3837_ = v___x_3820_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_key_3816_);
                    lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_value_3817_);
                    lean_ctor_set(v_reuseFailAlloc_3840_, 2, v___x_3835_);
                    v___x_3837_ = v_reuseFailAlloc_3840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3838_ = lean_array_uset(v_x_3814_, v___x_3834_, v___x_3837_);
                v_x_3814_ = v___x_3838_;
                v_x_3815_ = v_tail_3818_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(
    mut v_i_3842_: *mut LeanObject,
    mut v_source_3843_: *mut LeanObject,
    mut v_target_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v_es_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3845_ = lean_array_get_size(v_source_3843_);
                v___x_3846_ = lean_nat_dec_lt(v_i_3842_, v___x_3845_);
                if v___x_3846_ == 0 {
                    lean_dec_ref(v_source_3843_);
                    lean_dec(v_i_3842_);
                    return v_target_3844_;
                } else {
                    v_es_3847_ = lean_array_fget(v_source_3843_, v_i_3842_);
                    v___x_3848_ = lean_box(0);
                    v_source_3849_ = lean_array_fset(v_source_3843_, v_i_3842_, v___x_3848_);
                    v_target_3850_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_3844_, v_es_3847_);
                    v___x_3851_ = lean_unsigned_to_nat(1);
                    v___x_3852_ = lean_nat_add(v_i_3842_, v___x_3851_);
                    lean_dec(v_i_3842_);
                    v_i_3842_ = v___x_3852_;
                    v_source_3843_ = v_source_3849_;
                    v_target_3844_ = v_target_3850_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(
    mut v_data_3854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    v___x_3855_ = lean_array_get_size(v_data_3854_);
    v___x_3856_ = lean_unsigned_to_nat(2);
    v_nbuckets_3857_ = lean_nat_mul(v___x_3855_, v___x_3856_);
    v___x_3858_ = lean_unsigned_to_nat(0);
    v___x_3859_ = lean_box(0);
    v___x_3860_ = lean_mk_array(v_nbuckets_3857_, v___x_3859_);
    v___x_3861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_3858_, v_data_3854_, v___x_3860_);
    return v___x_3861_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(
    mut v_a_3862_: *mut LeanObject,
    mut v_b_3863_: *mut LeanObject,
    mut v_x_3864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v___x_3871_: u8 = 0;
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3864_) == 0 {
                    lean_dec(v_b_3863_);
                    lean_dec_ref(v_a_3862_);
                    return v_x_3864_;
                } else {
                    v_key_3865_ = lean_ctor_get(v_x_3864_, 0);
                    v_value_3866_ = lean_ctor_get(v_x_3864_, 1);
                    v_tail_3867_ = lean_ctor_get(v_x_3864_, 2);
                    v_isSharedCheck_3879_ = (!lean_is_exclusive(v_x_3864_)) as u8;
                    if v_isSharedCheck_3879_ == 0 {
                        v___x_3869_ = v_x_3864_;
                        v_isShared_3870_ = v_isSharedCheck_3879_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3867_);
                        lean_inc(v_value_3866_);
                        lean_inc(v_key_3865_);
                        lean_dec(v_x_3864_);
                        v___x_3869_ = lean_box(0);
                        v_isShared_3870_ = v_isSharedCheck_3879_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3871_ = l_Lean_ExprStructEq_beq(v_key_3865_, v_a_3862_);
                if v___x_3871_ == 0 {
                    v___x_3872_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_3862_, v_b_3863_, v_tail_3867_);
                    if v_isShared_3870_ == 0 {
                        lean_ctor_set(v___x_3869_, 2, v___x_3872_);
                        v___x_3874_ = v___x_3869_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_key_3865_);
                        lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_value_3866_);
                        lean_ctor_set(v_reuseFailAlloc_3875_, 2, v___x_3872_);
                        v___x_3874_ = v_reuseFailAlloc_3875_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3866_);
                    lean_dec(v_key_3865_);
                    if v_isShared_3870_ == 0 {
                        lean_ctor_set(v___x_3869_, 1, v_b_3863_);
                        lean_ctor_set(v___x_3869_, 0, v_a_3862_);
                        v___x_3877_ = v___x_3869_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3862_);
                        lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_b_3863_);
                        lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_tail_3867_);
                        v___x_3877_ = v_reuseFailAlloc_3878_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3874_;
            }
            3 => {
                return v___x_3877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(
    mut v_m_3880_: *mut LeanObject,
    mut v_a_3881_: *mut LeanObject,
    mut v_b_3882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3887_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: u64 = 0;
    let mut v___x_3890_: u64 = 0;
    let mut v___x_3891_: u64 = 0;
    let mut v_fold_3892_: u64 = 0;
    let mut v___x_3893_: u64 = 0;
    let mut v___x_3894_: u64 = 0;
    let mut v___x_3895_: u64 = 0;
    let mut v___x_3896_: usize = 0;
    let mut v___x_3897_: usize = 0;
    let mut v___x_3898_: usize = 0;
    let mut v___x_3899_: usize = 0;
    let mut v___x_3900_: usize = 0;
    let mut v_bkt_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: u8 = 0;
    let mut v_val_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3883_ = lean_ctor_get(v_m_3880_, 0);
                v_buckets_3884_ = lean_ctor_get(v_m_3880_, 1);
                v_isSharedCheck_3927_ = (!lean_is_exclusive(v_m_3880_)) as u8;
                if v_isSharedCheck_3927_ == 0 {
                    v___x_3886_ = v_m_3880_;
                    v_isShared_3887_ = v_isSharedCheck_3927_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3884_);
                    lean_inc(v_size_3883_);
                    lean_dec(v_m_3880_);
                    v___x_3886_ = lean_box(0);
                    v_isShared_3887_ = v_isSharedCheck_3927_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3888_ = lean_array_get_size(v_buckets_3884_);
                v___x_3889_ = l_Lean_ExprStructEq_hash(v_a_3881_);
                v___x_3890_ = 32u64;
                v___x_3891_ = lean_uint64_shift_right(v___x_3889_, v___x_3890_);
                v_fold_3892_ = lean_uint64_xor(v___x_3889_, v___x_3891_);
                v___x_3893_ = 16u64;
                v___x_3894_ = lean_uint64_shift_right(v_fold_3892_, v___x_3893_);
                v___x_3895_ = lean_uint64_xor(v_fold_3892_, v___x_3894_);
                v___x_3896_ = lean_uint64_to_usize(v___x_3895_);
                v___x_3897_ = lean_usize_of_nat(v___x_3888_);
                v___x_3898_ = 1usize;
                v___x_3899_ = lean_usize_sub(v___x_3897_, v___x_3898_);
                v___x_3900_ = lean_usize_land(v___x_3896_, v___x_3899_);
                v_bkt_3901_ = lean_array_uget_borrowed(v_buckets_3884_, v___x_3900_);
                v___x_3902_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_3881_, v_bkt_3901_);
                if v___x_3902_ == 0 {
                    v___x_3903_ = lean_unsigned_to_nat(1);
                    v_size_x27_3904_ = lean_nat_add(v_size_3883_, v___x_3903_);
                    lean_dec(v_size_3883_);
                    lean_inc(v_bkt_3901_);
                    v___x_3905_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3905_, 0, v_a_3881_);
                    lean_ctor_set(v___x_3905_, 1, v_b_3882_);
                    lean_ctor_set(v___x_3905_, 2, v_bkt_3901_);
                    v_buckets_x27_3906_ =
                        lean_array_uset(v_buckets_3884_, v___x_3900_, v___x_3905_);
                    v___x_3907_ = lean_unsigned_to_nat(4);
                    v___x_3908_ = lean_nat_mul(v_size_x27_3904_, v___x_3907_);
                    v___x_3909_ = lean_unsigned_to_nat(3);
                    v___x_3910_ = lean_nat_div(v___x_3908_, v___x_3909_);
                    lean_dec(v___x_3908_);
                    v___x_3911_ = lean_array_get_size(v_buckets_x27_3906_);
                    v___x_3912_ = lean_nat_dec_le(v___x_3910_, v___x_3911_);
                    lean_dec(v___x_3910_);
                    if v___x_3912_ == 0 {
                        v_val_3913_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_3906_);
                        if v_isShared_3887_ == 0 {
                            lean_ctor_set(v___x_3886_, 1, v_val_3913_);
                            lean_ctor_set(v___x_3886_, 0, v_size_x27_3904_);
                            v___x_3915_ = v___x_3886_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_size_x27_3904_);
                            lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_val_3913_);
                            v___x_3915_ = v_reuseFailAlloc_3916_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3887_ == 0 {
                            lean_ctor_set(v___x_3886_, 1, v_buckets_x27_3906_);
                            lean_ctor_set(v___x_3886_, 0, v_size_x27_3904_);
                            v___x_3918_ = v___x_3886_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_size_x27_3904_);
                            lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_buckets_x27_3906_);
                            v___x_3918_ = v_reuseFailAlloc_3919_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3901_);
                    v___x_3920_ = lean_box(0);
                    v_buckets_x27_3921_ =
                        lean_array_uset(v_buckets_3884_, v___x_3900_, v___x_3920_);
                    v___x_3922_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_3881_, v_b_3882_, v_bkt_3901_);
                    v___x_3923_ = lean_array_uset(v_buckets_x27_3921_, v___x_3900_, v___x_3922_);
                    if v_isShared_3887_ == 0 {
                        lean_ctor_set(v___x_3886_, 1, v___x_3923_);
                        v___x_3925_ = v___x_3886_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_size_3883_);
                        lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___x_3923_);
                        v___x_3925_ = v_reuseFailAlloc_3926_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3915_;
            }
            3 => {
                return v___x_3918_;
            }
            4 => {
                return v___x_3925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(
    mut v_a_3928_: *mut LeanObject,
    mut v_e_3929_: *mut LeanObject,
    mut v_a_3930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    v___x_3932_ = lean_st_ref_take(v_a_3928_);
    v___x_3933_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_3932_, v_e_3929_, v_a_3930_);
    v___x_3934_ = lean_st_ref_set(v_a_3928_, v___x_3933_);
    v___x_3935_ = lean_box(0);
    return v___x_3935_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(
    mut v_a_3936_: *mut LeanObject,
    mut v_e_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3940_: *mut LeanObject = core::ptr::null_mut();
    v_res_3940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_3936_, v_e_3937_, v_a_3938_);
    lean_dec(v_a_3936_);
    return v_res_3940_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(
    mut v_fvars_3944_: *mut LeanObject,
    mut v_pre_3945_: *mut LeanObject,
    mut v_post_3946_: *mut LeanObject,
    mut v_usedLetOnly_3947_: u8,
    mut v_skipConstInApp_3948_: u8,
    mut v_skipInstances_3949_: u8,
    mut v_body_3950_: *mut LeanObject,
    mut v_x_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    v___x_3958_ = lean_array_push(v_fvars_3944_, v_x_3951_);
    v___x_3959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_3945_, v_post_3946_, v_usedLetOnly_3947_, v_skipConstInApp_3948_, v_skipInstances_3949_, v___x_3958_, v_body_3950_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
    return v___x_3959_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(
    mut v_fvars_3960_: *mut LeanObject,
    mut v_pre_3961_: *mut LeanObject,
    mut v_post_3962_: *mut LeanObject,
    mut v_usedLetOnly_3963_: *mut LeanObject,
    mut v_skipConstInApp_3964_: *mut LeanObject,
    mut v_skipInstances_3965_: *mut LeanObject,
    mut v_body_3966_: *mut LeanObject,
    mut v_x_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
    mut v___y_3971_: *mut LeanObject,
    mut v___y_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_3974_: u8 = 0;
    let mut v_skipConstInApp_boxed_3975_: u8 = 0;
    let mut v_skipInstances_boxed_3976_: u8 = 0;
    let mut v_res_3977_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_3974_ = (lean_unbox(v_usedLetOnly_3963_) as u8);
    v_skipConstInApp_boxed_3975_ = (lean_unbox(v_skipConstInApp_3964_) as u8);
    v_skipInstances_boxed_3976_ = (lean_unbox(v_skipInstances_3965_) as u8);
    v_res_3977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_3960_, v_pre_3961_, v_post_3962_, v_usedLetOnly_boxed_3974_, v_skipConstInApp_boxed_3975_, v_skipInstances_boxed_3976_, v_body_3966_, v_x_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
    lean_dec(v___y_3972_);
    lean_dec_ref(v___y_3971_);
    lean_dec(v___y_3970_);
    lean_dec_ref(v___y_3969_);
    lean_dec(v___y_3968_);
    return v_res_3977_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(
    mut v_pre_3978_: *mut LeanObject,
    mut v_post_3979_: *mut LeanObject,
    mut v_usedLetOnly_3980_: u8,
    mut v_skipConstInApp_3981_: u8,
    mut v_skipInstances_3982_: u8,
    mut v_e_3983_: *mut LeanObject,
    mut v_a_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3994_: u8 = 0;
    let mut v_e_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut v_a_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4013_: u8 = 0;
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_post_3979_);
                lean_inc(v___y_3988_);
                lean_inc_ref(v___y_3987_);
                lean_inc(v___y_3986_);
                lean_inc_ref(v___y_3985_);
                lean_inc_ref(v_e_3983_);
                v___x_3990_ = lean_apply_6(
                    v_post_3979_,
                    v_e_3983_,
                    v___y_3985_,
                    v___y_3986_,
                    v___y_3987_,
                    v___y_3988_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3990_) == 0 {
                    v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
                    v_isSharedCheck_4009_ = (!lean_is_exclusive(v___x_3990_)) as u8;
                    if v_isSharedCheck_4009_ == 0 {
                        v___x_3993_ = v___x_3990_;
                        v_isShared_3994_ = v_isSharedCheck_4009_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3991_);
                        lean_dec(v___x_3990_);
                        v___x_3993_ = lean_box(0);
                        v_isShared_3994_ = v_isSharedCheck_4009_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3983_);
                    lean_dec_ref(v_post_3979_);
                    lean_dec_ref(v_pre_3978_);
                    v_a_4010_ = lean_ctor_get(v___x_3990_, 0);
                    v_isSharedCheck_4017_ = (!lean_is_exclusive(v___x_3990_)) as u8;
                    if v_isSharedCheck_4017_ == 0 {
                        v___x_4012_ = v___x_3990_;
                        v_isShared_4013_ = v_isSharedCheck_4017_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4010_);
                        lean_dec(v___x_3990_);
                        v___x_4012_ = lean_box(0);
                        v_isShared_4013_ = v_isSharedCheck_4017_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_3991_) {
                0 => {
                    lean_dec_ref(v_e_3983_);
                    lean_dec_ref(v_post_3979_);
                    lean_dec_ref(v_pre_3978_);
                    v_e_3995_ = lean_ctor_get(v_a_3991_, 0);
                    lean_inc_ref(v_e_3995_);
                    lean_dec_ref_known(v_a_3991_, 1);
                    if v_isShared_3994_ == 0 {
                        lean_ctor_set(v___x_3993_, 0, v_e_3995_);
                        v___x_3997_ = v___x_3993_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_e_3995_);
                        v___x_3997_ = v_reuseFailAlloc_3998_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_3993_);
                    lean_dec_ref(v_e_3983_);
                    v_e_3999_ = lean_ctor_get(v_a_3991_, 0);
                    lean_inc_ref(v_e_3999_);
                    lean_dec_ref_known(v_a_3991_, 1);
                    v___x_4000_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_3978_, v_post_3979_, v_usedLetOnly_3980_, v_skipConstInApp_3981_, v_skipInstances_3982_, v_e_3999_, v_a_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
                    return v___x_4000_;
                }
                _ => {
                    lean_dec_ref(v_post_3979_);
                    lean_dec_ref(v_pre_3978_);
                    v_e_x3f_4001_ = lean_ctor_get(v_a_3991_, 0);
                    lean_inc(v_e_x3f_4001_);
                    lean_dec_ref_known(v_a_3991_, 1);
                    if lean_obj_tag(v_e_x3f_4001_) == 0 {
                        if v_isShared_3994_ == 0 {
                            lean_ctor_set(v___x_3993_, 0, v_e_3983_);
                            v___x_4003_ = v___x_3993_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_e_3983_);
                            v___x_4003_ = v_reuseFailAlloc_4004_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_3983_);
                        v_val_4005_ = lean_ctor_get(v_e_x3f_4001_, 0);
                        lean_inc(v_val_4005_);
                        lean_dec_ref_known(v_e_x3f_4001_, 1);
                        if v_isShared_3994_ == 0 {
                            lean_ctor_set(v___x_3993_, 0, v_val_4005_);
                            v___x_4007_ = v___x_3993_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_val_4005_);
                            v___x_4007_ = v_reuseFailAlloc_4008_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_3997_;
            }
            3 => {
                return v___x_4003_;
            }
            4 => {
                return v___x_4007_;
            }
            5 => {
                if v_isShared_4013_ == 0 {
                    v___x_4015_ = v___x_4012_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
                    v___x_4015_ = v_reuseFailAlloc_4016_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(
    mut v_pre_4018_: *mut LeanObject,
    mut v_post_4019_: *mut LeanObject,
    mut v_usedLetOnly_4020_: u8,
    mut v_skipConstInApp_4021_: u8,
    mut v_skipInstances_4022_: u8,
    mut v_fvars_4023_: *mut LeanObject,
    mut v_e_4024_: *mut LeanObject,
    mut v_a_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_4024_) == 6 {
        let mut v_binderName_4031_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_4032_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_4033_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_4034_: u8 = 0;
        let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_4031_ = lean_ctor_get(v_e_4024_, 0);
        lean_inc(v_binderName_4031_);
        v_binderType_4032_ = lean_ctor_get(v_e_4024_, 1);
        lean_inc_ref(v_binderType_4032_);
        v_body_4033_ = lean_ctor_get(v_e_4024_, 2);
        lean_inc_ref(v_body_4033_);
        v_binderInfo_4034_ = lean_ctor_get_uint8(
            v_e_4024_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_e_4024_, 3);
        v___x_4035_ = lean_expr_instantiate_rev(v_binderType_4032_, v_fvars_4023_);
        lean_dec_ref(v_binderType_4032_);
        lean_inc_ref(v_post_4019_);
        lean_inc_ref(v_pre_4018_);
        v___x_4036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4018_, v_post_4019_, v_usedLetOnly_4020_, v_skipConstInApp_4021_, v_skipInstances_4022_, v___x_4035_, v_a_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
        if lean_obj_tag(v___x_4036_) == 0 {
            let mut v_a_4037_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4041_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4042_: u8 = 0;
            let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
            v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
            lean_inc(v_a_4037_);
            lean_dec_ref_known(v___x_4036_, 1);
            v___x_4038_ = lean_box((v_usedLetOnly_4020_) as usize);
            v___x_4039_ = lean_box((v_skipConstInApp_4021_) as usize);
            v___x_4040_ = lean_box((v_skipInstances_4022_) as usize);
            v___f_4041_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            lean_closure_set(v___f_4041_, 0, v_fvars_4023_);
            lean_closure_set(v___f_4041_, 1, v_pre_4018_);
            lean_closure_set(v___f_4041_, 2, v_post_4019_);
            lean_closure_set(v___f_4041_, 3, v___x_4038_);
            lean_closure_set(v___f_4041_, 4, v___x_4039_);
            lean_closure_set(v___f_4041_, 5, v___x_4040_);
            lean_closure_set(v___f_4041_, 6, v_body_4033_);
            v___x_4042_ = 0;
            v___x_4043_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_4031_, v_binderInfo_4034_, v_a_4037_, v___f_4041_, v___x_4042_, v_a_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
            return v___x_4043_;
        } else {
            lean_dec_ref(v_body_4033_);
            lean_dec(v_binderName_4031_);
            lean_dec_ref(v_fvars_4023_);
            lean_dec_ref(v_post_4019_);
            lean_dec_ref(v_pre_4018_);
            return v___x_4036_;
        }
    } else {
        let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
        v___x_4044_ = lean_expr_instantiate_rev(v_e_4024_, v_fvars_4023_);
        lean_dec_ref(v_e_4024_);
        lean_inc_ref(v_post_4019_);
        lean_inc_ref(v_pre_4018_);
        v___x_4045_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4018_, v_post_4019_, v_usedLetOnly_4020_, v_skipConstInApp_4021_, v_skipInstances_4022_, v___x_4044_, v_a_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
        if lean_obj_tag(v___x_4045_) == 0 {
            let mut v_a_4046_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4047_: u8 = 0;
            let mut v___x_4048_: u8 = 0;
            let mut v___x_4049_: u8 = 0;
            let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
            v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
            lean_inc(v_a_4046_);
            lean_dec_ref_known(v___x_4045_, 1);
            v___x_4047_ = 0;
            v___x_4048_ = 1;
            v___x_4049_ = 1;
            v___x_4050_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_4023_,
                v_a_4046_,
                v___x_4047_,
                v_usedLetOnly_4020_,
                v___x_4047_,
                v___x_4048_,
                v___x_4049_,
                v___y_4026_,
                v___y_4027_,
                v___y_4028_,
                v___y_4029_,
            );
            lean_dec_ref(v_fvars_4023_);
            if lean_obj_tag(v___x_4050_) == 0 {
                let mut v_a_4051_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
                v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
                lean_inc(v_a_4051_);
                lean_dec_ref_known(v___x_4050_, 1);
                v___x_4052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4018_, v_post_4019_, v_usedLetOnly_4020_, v_skipConstInApp_4021_, v_skipInstances_4022_, v_a_4051_, v_a_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
                return v___x_4052_;
            } else {
                lean_dec_ref(v_post_4019_);
                lean_dec_ref(v_pre_4018_);
                return v___x_4050_;
            }
        } else {
            lean_dec_ref(v_fvars_4023_);
            lean_dec_ref(v_post_4019_);
            lean_dec_ref(v_pre_4018_);
            return v___x_4045_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(
    mut v_fvars_4053_: *mut LeanObject,
    mut v_pre_4054_: *mut LeanObject,
    mut v_post_4055_: *mut LeanObject,
    mut v_usedLetOnly_4056_: u8,
    mut v_skipConstInApp_4057_: u8,
    mut v_skipInstances_4058_: u8,
    mut v_body_4059_: *mut LeanObject,
    mut v_x_4060_: *mut LeanObject,
    mut v___y_4061_: *mut LeanObject,
    mut v___y_4062_: *mut LeanObject,
    mut v___y_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    v___x_4067_ = lean_array_push(v_fvars_4053_, v_x_4060_);
    v___x_4068_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_4054_, v_post_4055_, v_usedLetOnly_4056_, v_skipConstInApp_4057_, v_skipInstances_4058_, v___x_4067_, v_body_4059_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
    return v___x_4068_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(
    mut v_fvars_4069_: *mut LeanObject,
    mut v_pre_4070_: *mut LeanObject,
    mut v_post_4071_: *mut LeanObject,
    mut v_usedLetOnly_4072_: *mut LeanObject,
    mut v_skipConstInApp_4073_: *mut LeanObject,
    mut v_skipInstances_4074_: *mut LeanObject,
    mut v_body_4075_: *mut LeanObject,
    mut v_x_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4083_: u8 = 0;
    let mut v_skipConstInApp_boxed_4084_: u8 = 0;
    let mut v_skipInstances_boxed_4085_: u8 = 0;
    let mut v_res_4086_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4083_ = (lean_unbox(v_usedLetOnly_4072_) as u8);
    v_skipConstInApp_boxed_4084_ = (lean_unbox(v_skipConstInApp_4073_) as u8);
    v_skipInstances_boxed_4085_ = (lean_unbox(v_skipInstances_4074_) as u8);
    v_res_4086_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_4069_, v_pre_4070_, v_post_4071_, v_usedLetOnly_boxed_4083_, v_skipConstInApp_boxed_4084_, v_skipInstances_boxed_4085_, v_body_4075_, v_x_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
    lean_dec(v___y_4081_);
    lean_dec_ref(v___y_4080_);
    lean_dec(v___y_4079_);
    lean_dec_ref(v___y_4078_);
    lean_dec(v___y_4077_);
    return v_res_4086_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(
    mut v_pre_4087_: *mut LeanObject,
    mut v_post_4088_: *mut LeanObject,
    mut v_usedLetOnly_4089_: u8,
    mut v_skipConstInApp_4090_: u8,
    mut v_skipInstances_4091_: u8,
    mut v_fvars_4092_: *mut LeanObject,
    mut v_e_4093_: *mut LeanObject,
    mut v_a_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_4093_) == 8 {
        let mut v_declName_4100_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_4101_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_4102_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_4103_: *mut LeanObject = core::ptr::null_mut();
        let mut v_nondep_4104_: u8 = 0;
        let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
        v_declName_4100_ = lean_ctor_get(v_e_4093_, 0);
        lean_inc(v_declName_4100_);
        v_type_4101_ = lean_ctor_get(v_e_4093_, 1);
        lean_inc_ref(v_type_4101_);
        v_value_4102_ = lean_ctor_get(v_e_4093_, 2);
        lean_inc_ref(v_value_4102_);
        v_body_4103_ = lean_ctor_get(v_e_4093_, 3);
        lean_inc_ref(v_body_4103_);
        v_nondep_4104_ = lean_ctor_get_uint8(
            v_e_4093_,
            (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
        );
        lean_dec_ref_known(v_e_4093_, 4);
        v___x_4105_ = lean_expr_instantiate_rev(v_type_4101_, v_fvars_4092_);
        lean_dec_ref(v_type_4101_);
        lean_inc_ref(v_post_4088_);
        lean_inc_ref(v_pre_4087_);
        v___x_4106_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4087_, v_post_4088_, v_usedLetOnly_4089_, v_skipConstInApp_4090_, v_skipInstances_4091_, v___x_4105_, v_a_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
        if lean_obj_tag(v___x_4106_) == 0 {
            let mut v_a_4107_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
            v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
            lean_inc(v_a_4107_);
            lean_dec_ref_known(v___x_4106_, 1);
            v___x_4108_ = lean_expr_instantiate_rev(v_value_4102_, v_fvars_4092_);
            lean_dec_ref(v_value_4102_);
            lean_inc_ref(v_post_4088_);
            lean_inc_ref(v_pre_4087_);
            v___x_4109_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4087_, v_post_4088_, v_usedLetOnly_4089_, v_skipConstInApp_4090_, v_skipInstances_4091_, v___x_4108_, v_a_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
            if lean_obj_tag(v___x_4109_) == 0 {
                let mut v_a_4110_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_4114_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4115_: u8 = 0;
                let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
                v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
                lean_inc(v_a_4110_);
                lean_dec_ref_known(v___x_4109_, 1);
                v___x_4111_ = lean_box((v_usedLetOnly_4089_) as usize);
                v___x_4112_ = lean_box((v_skipConstInApp_4090_) as usize);
                v___x_4113_ = lean_box((v_skipInstances_4091_) as usize);
                v___f_4114_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                lean_closure_set(v___f_4114_, 0, v_fvars_4092_);
                lean_closure_set(v___f_4114_, 1, v_pre_4087_);
                lean_closure_set(v___f_4114_, 2, v_post_4088_);
                lean_closure_set(v___f_4114_, 3, v___x_4111_);
                lean_closure_set(v___f_4114_, 4, v___x_4112_);
                lean_closure_set(v___f_4114_, 5, v___x_4113_);
                lean_closure_set(v___f_4114_, 6, v_body_4103_);
                v___x_4115_ = 0;
                v___x_4116_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_4100_, v_a_4107_, v_a_4110_, v___f_4114_, v_nondep_4104_, v___x_4115_, v_a_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
                return v___x_4116_;
            } else {
                lean_dec(v_a_4107_);
                lean_dec_ref(v_body_4103_);
                lean_dec(v_declName_4100_);
                lean_dec_ref(v_fvars_4092_);
                lean_dec_ref(v_post_4088_);
                lean_dec_ref(v_pre_4087_);
                return v___x_4109_;
            }
        } else {
            lean_dec_ref(v_body_4103_);
            lean_dec_ref(v_value_4102_);
            lean_dec(v_declName_4100_);
            lean_dec_ref(v_fvars_4092_);
            lean_dec_ref(v_post_4088_);
            lean_dec_ref(v_pre_4087_);
            return v___x_4106_;
        }
    } else {
        let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
        v___x_4117_ = lean_expr_instantiate_rev(v_e_4093_, v_fvars_4092_);
        lean_dec_ref(v_e_4093_);
        lean_inc_ref(v_post_4088_);
        lean_inc_ref(v_pre_4087_);
        v___x_4118_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4087_, v_post_4088_, v_usedLetOnly_4089_, v_skipConstInApp_4090_, v_skipInstances_4091_, v___x_4117_, v_a_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
        if lean_obj_tag(v___x_4118_) == 0 {
            let mut v_a_4119_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4120_: u8 = 0;
            let mut v___x_4121_: u8 = 0;
            let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
            v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
            lean_inc(v_a_4119_);
            lean_dec_ref_known(v___x_4118_, 1);
            v___x_4120_ = 0;
            v___x_4121_ = 1;
            v___x_4122_ = l_Lean_Meta_mkLetFVars(
                v_fvars_4092_,
                v_a_4119_,
                v_usedLetOnly_4089_,
                v___x_4120_,
                v___x_4121_,
                v___y_4095_,
                v___y_4096_,
                v___y_4097_,
                v___y_4098_,
            );
            lean_dec_ref(v_fvars_4092_);
            if lean_obj_tag(v___x_4122_) == 0 {
                let mut v_a_4123_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
                v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
                lean_inc(v_a_4123_);
                lean_dec_ref_known(v___x_4122_, 1);
                v___x_4124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4087_, v_post_4088_, v_usedLetOnly_4089_, v_skipConstInApp_4090_, v_skipInstances_4091_, v_a_4123_, v_a_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
                return v___x_4124_;
            } else {
                lean_dec_ref(v_post_4088_);
                lean_dec_ref(v_pre_4087_);
                return v___x_4122_;
            }
        } else {
            lean_dec_ref(v_fvars_4092_);
            lean_dec_ref(v_post_4088_);
            lean_dec_ref(v_pre_4087_);
            return v___x_4118_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(
    mut v_pre_4125_: *mut LeanObject,
    mut v_post_4126_: *mut LeanObject,
    mut v_usedLetOnly_4127_: u8,
    mut v_skipConstInApp_4128_: u8,
    mut v_skipInstances_4129_: u8,
    mut v_sz_4130_: usize,
    mut v_i_4131_: usize,
    mut v_bs_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
    mut v___y_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4139_: u8 = 0;
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: usize = 0;
    let mut v___x_4147_: usize = 0;
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4139_ = lean_usize_dec_lt(v_i_4131_, v_sz_4130_);
                if v___x_4139_ == 0 {
                    lean_dec_ref(v_post_4126_);
                    lean_dec_ref(v_pre_4125_);
                    v___x_4140_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4140_, 0, v_bs_4132_);
                    return v___x_4140_;
                } else {
                    v_v_4141_ = lean_array_uget_borrowed(v_bs_4132_, v_i_4131_);
                    lean_inc(v_v_4141_);
                    lean_inc_ref(v_post_4126_);
                    lean_inc_ref(v_pre_4125_);
                    v___x_4142_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4125_, v_post_4126_, v_usedLetOnly_4127_, v_skipConstInApp_4128_, v_skipInstances_4129_, v_v_4141_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
                    if lean_obj_tag(v___x_4142_) == 0 {
                        v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
                        lean_inc(v_a_4143_);
                        lean_dec_ref_known(v___x_4142_, 1);
                        v___x_4144_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4145_ = lean_array_uset(v_bs_4132_, v_i_4131_, v___x_4144_);
                        v___x_4146_ = 1usize;
                        v___x_4147_ = lean_usize_add(v_i_4131_, v___x_4146_);
                        v___x_4148_ = lean_array_uset(v_bs_x27_4145_, v_i_4131_, v_a_4143_);
                        v_i_4131_ = v___x_4147_;
                        v_bs_4132_ = v___x_4148_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_4132_);
                        lean_dec_ref(v_post_4126_);
                        lean_dec_ref(v_pre_4125_);
                        v_a_4150_ = lean_ctor_get(v___x_4142_, 0);
                        v_isSharedCheck_4157_ = (!lean_is_exclusive(v___x_4142_)) as u8;
                        if v_isSharedCheck_4157_ == 0 {
                            v___x_4152_ = v___x_4142_;
                            v_isShared_4153_ = v_isSharedCheck_4157_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4150_);
                            lean_dec(v___x_4142_);
                            v___x_4152_ = lean_box(0);
                            v_isShared_4153_ = v_isSharedCheck_4157_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4153_ == 0 {
                    v___x_4155_ = v___x_4152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
                    v___x_4155_ = v_reuseFailAlloc_4156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(
    mut v_pre_4158_: *mut LeanObject,
    mut v_post_4159_: *mut LeanObject,
    mut v_usedLetOnly_4160_: u8,
    mut v_skipConstInApp_4161_: u8,
    mut v_skipInstances_4162_: u8,
    mut v___x_4163_: *mut LeanObject,
    mut v___y_4164_: *mut LeanObject,
    mut v_b_4165_: *mut LeanObject,
    mut v_a_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v_a_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4158_, v_post_4159_, v_usedLetOnly_4160_, v_skipConstInApp_4161_, v_skipInstances_4162_, v___x_4163_, v___y_4164_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
                if lean_obj_tag(v___x_4172_) == 0 {
                    v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
                    v_isSharedCheck_4182_ = (!lean_is_exclusive(v___x_4172_)) as u8;
                    if v_isSharedCheck_4182_ == 0 {
                        v___x_4175_ = v___x_4172_;
                        v_isShared_4176_ = v_isSharedCheck_4182_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4173_);
                        lean_dec(v___x_4172_);
                        v___x_4175_ = lean_box(0);
                        v_isShared_4176_ = v_isSharedCheck_4182_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_4165_);
                    v_a_4183_ = lean_ctor_get(v___x_4172_, 0);
                    v_isSharedCheck_4190_ = (!lean_is_exclusive(v___x_4172_)) as u8;
                    if v_isSharedCheck_4190_ == 0 {
                        v___x_4185_ = v___x_4172_;
                        v_isShared_4186_ = v_isSharedCheck_4190_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4183_);
                        lean_dec(v___x_4172_);
                        v___x_4185_ = lean_box(0);
                        v_isShared_4186_ = v_isSharedCheck_4190_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4177_ = lean_array_fset(v_b_4165_, v_a_4166_, v_a_4173_);
                v___x_4178_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4178_, 0, v___x_4177_);
                if v_isShared_4176_ == 0 {
                    lean_ctor_set(v___x_4175_, 0, v___x_4178_);
                    v___x_4180_ = v___x_4175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
                    v___x_4180_ = v_reuseFailAlloc_4181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4180_;
            }
            3 => {
                if v_isShared_4186_ == 0 {
                    v___x_4188_ = v___x_4185_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
                    v___x_4188_ = v_reuseFailAlloc_4189_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(
    mut v_pre_4191_: *mut LeanObject,
    mut v_post_4192_: *mut LeanObject,
    mut v_usedLetOnly_4193_: *mut LeanObject,
    mut v_skipConstInApp_4194_: *mut LeanObject,
    mut v_skipInstances_4195_: *mut LeanObject,
    mut v___x_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v_b_4198_: *mut LeanObject,
    mut v_a_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4205_: u8 = 0;
    let mut v_skipConstInApp_boxed_4206_: u8 = 0;
    let mut v_skipInstances_boxed_4207_: u8 = 0;
    let mut v_res_4208_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4205_ = (lean_unbox(v_usedLetOnly_4193_) as u8);
    v_skipConstInApp_boxed_4206_ = (lean_unbox(v_skipConstInApp_4194_) as u8);
    v_skipInstances_boxed_4207_ = (lean_unbox(v_skipInstances_4195_) as u8);
    v_res_4208_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_4191_, v_post_4192_, v_usedLetOnly_boxed_4205_, v_skipConstInApp_boxed_4206_, v_skipInstances_boxed_4207_, v___x_4196_, v___y_4197_, v_b_4198_, v_a_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
    lean_dec(v___y_4203_);
    lean_dec_ref(v___y_4202_);
    lean_dec(v___y_4201_);
    lean_dec_ref(v___y_4200_);
    lean_dec(v_a_4199_);
    lean_dec(v___y_4197_);
    return v_res_4208_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(
    mut v_upperBound_4209_: *mut LeanObject,
    mut v___x_4210_: *mut LeanObject,
    mut v_pre_4211_: *mut LeanObject,
    mut v_post_4212_: *mut LeanObject,
    mut v_usedLetOnly_4213_: u8,
    mut v_skipConstInApp_4214_: u8,
    mut v_skipInstances_4215_: u8,
    mut v_a_4216_: *mut LeanObject,
    mut v_b_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v_a_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4239_: u8 = 0;
    let mut v_a_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v___x_4248_: u8 = 0;
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_4258_: u8 = 0;
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4248_ = lean_nat_dec_lt(v_a_4216_, v_upperBound_4209_);
                if v___x_4248_ == 0 {
                    lean_dec(v_a_4216_);
                    lean_dec_ref(v_post_4212_);
                    lean_dec_ref(v_pre_4211_);
                    v___x_4249_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4249_, 0, v_b_4217_);
                    return v___x_4249_;
                } else {
                    v___x_4250_ = lean_array_fget_borrowed(v_b_4217_, v_a_4216_);
                    v___x_4251_ = lean_array_get_size(v___x_4210_);
                    v___x_4252_ = lean_nat_dec_lt(v_a_4216_, v___x_4251_);
                    if v___x_4252_ == 0 {
                        lean_inc(v___x_4250_);
                        v___x_4253_ = lean_box((v_usedLetOnly_4213_) as usize);
                        v___x_4254_ = lean_box((v_skipConstInApp_4214_) as usize);
                        v___x_4255_ = lean_box((v_skipInstances_4215_) as usize);
                        lean_inc(v_a_4216_);
                        lean_inc(v___y_4218_);
                        lean_inc_ref(v_post_4212_);
                        lean_inc_ref(v_pre_4211_);
                        v___f_4256_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                        lean_closure_set(v___f_4256_, 0, v_pre_4211_);
                        lean_closure_set(v___f_4256_, 1, v_post_4212_);
                        lean_closure_set(v___f_4256_, 2, v___x_4253_);
                        lean_closure_set(v___f_4256_, 3, v___x_4254_);
                        lean_closure_set(v___f_4256_, 4, v___x_4255_);
                        lean_closure_set(v___f_4256_, 5, v___x_4250_);
                        lean_closure_set(v___f_4256_, 6, v___y_4218_);
                        lean_closure_set(v___f_4256_, 7, v_b_4217_);
                        lean_closure_set(v___f_4256_, 8, v_a_4216_);
                        v___y_4225_ = v___f_4256_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4257_ = lean_array_fget_borrowed(v___x_4210_, v_a_4216_);
                        v_isInstance_4258_ = lean_ctor_get_uint8(
                            v___x_4257_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_4258_ == 0 {
                            lean_inc(v___x_4250_);
                            v___x_4259_ = lean_box((v_usedLetOnly_4213_) as usize);
                            v___x_4260_ = lean_box((v_skipConstInApp_4214_) as usize);
                            v___x_4261_ = lean_box((v_skipInstances_4215_) as usize);
                            lean_inc(v_a_4216_);
                            lean_inc(v___y_4218_);
                            lean_inc_ref(v_post_4212_);
                            lean_inc_ref(v_pre_4211_);
                            v___f_4262_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                            lean_closure_set(v___f_4262_, 0, v_pre_4211_);
                            lean_closure_set(v___f_4262_, 1, v_post_4212_);
                            lean_closure_set(v___f_4262_, 2, v___x_4259_);
                            lean_closure_set(v___f_4262_, 3, v___x_4260_);
                            lean_closure_set(v___f_4262_, 4, v___x_4261_);
                            lean_closure_set(v___f_4262_, 5, v___x_4250_);
                            lean_closure_set(v___f_4262_, 6, v___y_4218_);
                            lean_closure_set(v___f_4262_, 7, v_b_4217_);
                            lean_closure_set(v___f_4262_, 8, v_a_4216_);
                            v___y_4225_ = v___f_4262_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4263_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4263_, 0, v_b_4217_);
                            v___f_4264_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 1);
                            lean_closure_set(v___f_4264_, 0, v___x_4263_);
                            v___y_4225_ = v___f_4264_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v___y_4222_);
                lean_inc_ref(v___y_4221_);
                lean_inc(v___y_4220_);
                lean_inc_ref(v___y_4219_);
                v___x_4226_ = lean_apply_5(
                    v___y_4225_,
                    v___y_4219_,
                    v___y_4220_,
                    v___y_4221_,
                    v___y_4222_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4226_) == 0 {
                    v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
                    v_isSharedCheck_4239_ = (!lean_is_exclusive(v___x_4226_)) as u8;
                    if v_isSharedCheck_4239_ == 0 {
                        v___x_4229_ = v___x_4226_;
                        v_isShared_4230_ = v_isSharedCheck_4239_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4227_);
                        lean_dec(v___x_4226_);
                        v___x_4229_ = lean_box(0);
                        v_isShared_4230_ = v_isSharedCheck_4239_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4216_);
                    lean_dec_ref(v_post_4212_);
                    lean_dec_ref(v_pre_4211_);
                    v_a_4240_ = lean_ctor_get(v___x_4226_, 0);
                    v_isSharedCheck_4247_ = (!lean_is_exclusive(v___x_4226_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v___x_4242_ = v___x_4226_;
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4240_);
                        lean_dec(v___x_4226_);
                        v___x_4242_ = lean_box(0);
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4227_) == 0 {
                    lean_dec(v_a_4216_);
                    lean_dec_ref(v_post_4212_);
                    lean_dec_ref(v_pre_4211_);
                    v_a_4231_ = lean_ctor_get(v_a_4227_, 0);
                    lean_inc(v_a_4231_);
                    lean_dec_ref_known(v_a_4227_, 1);
                    if v_isShared_4230_ == 0 {
                        lean_ctor_set(v___x_4229_, 0, v_a_4231_);
                        v___x_4233_ = v___x_4229_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4231_);
                        v___x_4233_ = v_reuseFailAlloc_4234_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4229_);
                    v_a_4235_ = lean_ctor_get(v_a_4227_, 0);
                    lean_inc(v_a_4235_);
                    lean_dec_ref_known(v_a_4227_, 1);
                    v___x_4236_ = lean_unsigned_to_nat(1);
                    v___x_4237_ = lean_nat_add(v_a_4216_, v___x_4236_);
                    lean_dec(v_a_4216_);
                    v_a_4216_ = v___x_4237_;
                    v_b_4217_ = v_a_4235_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4233_;
            }
            4 => {
                if v_isShared_4243_ == 0 {
                    v___x_4245_ = v___x_4242_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(
    mut v_skipInstances_4265_: u8,
    mut v_pre_4266_: *mut LeanObject,
    mut v_post_4267_: *mut LeanObject,
    mut v_usedLetOnly_4268_: u8,
    mut v_skipConstInApp_4269_: u8,
    mut v_x_4270_: *mut LeanObject,
    mut v_x_4271_: *mut LeanObject,
    mut v_x_4272_: *mut LeanObject,
    mut v___y_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4286_: usize = 0;
    let mut v___x_4287_: usize = 0;
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4312_: u8 = 0;
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4316_: u8 = 0;
    let mut v_a_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4320_: u8 = 0;
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4324_: u8 = 0;
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4270_) == 5 {
                    v_fn_4328_ = lean_ctor_get(v_x_4270_, 0);
                    lean_inc_ref(v_fn_4328_);
                    v_arg_4329_ = lean_ctor_get(v_x_4270_, 1);
                    lean_inc_ref(v_arg_4329_);
                    lean_dec_ref_known(v_x_4270_, 2);
                    v___x_4330_ = lean_array_set(v_x_4271_, v_x_4272_, v_arg_4329_);
                    v___x_4331_ = lean_unsigned_to_nat(1);
                    v___x_4332_ = lean_nat_sub(v_x_4272_, v___x_4331_);
                    lean_dec(v_x_4272_);
                    v_x_4270_ = v_fn_4328_;
                    v_x_4271_ = v___x_4330_;
                    v_x_4272_ = v___x_4332_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_4272_);
                    if v_skipConstInApp_4269_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_4334_ = l_Lean_Expr_isConst(v_x_4270_);
                        if v___x_4334_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_4280_ = v_x_4270_;
                            v___y_4281_ = v___y_4273_;
                            v___y_4282_ = v___y_4274_;
                            v___y_4283_ = v___y_4275_;
                            v___y_4284_ = v___y_4276_;
                            v___y_4285_ = v___y_4277_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_4265_ == 0 {
                    v_sz_4286_ = lean_array_size(v_x_4271_);
                    v___x_4287_ = 0usize;
                    lean_inc_ref(v_post_4267_);
                    lean_inc_ref(v_pre_4266_);
                    v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_4266_, v_post_4267_, v_usedLetOnly_4268_, v_skipConstInApp_4269_, v_skipInstances_4265_, v_sz_4286_, v___x_4287_, v_x_4271_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
                    if lean_obj_tag(v___x_4288_) == 0 {
                        v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
                        lean_inc(v_a_4289_);
                        lean_dec_ref_known(v___x_4288_, 1);
                        v___x_4290_ = l_Lean_mkAppN(v_f_4280_, v_a_4289_);
                        lean_dec(v_a_4289_);
                        v___x_4291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4266_, v_post_4267_, v_usedLetOnly_4268_, v_skipConstInApp_4269_, v_skipInstances_4265_, v___x_4290_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
                        return v___x_4291_;
                    } else {
                        lean_dec_ref(v_f_4280_);
                        lean_dec_ref(v_post_4267_);
                        lean_dec_ref(v_pre_4266_);
                        v_a_4292_ = lean_ctor_get(v___x_4288_, 0);
                        v_isSharedCheck_4299_ = (!lean_is_exclusive(v___x_4288_)) as u8;
                        if v_isSharedCheck_4299_ == 0 {
                            v___x_4294_ = v___x_4288_;
                            v_isShared_4295_ = v_isSharedCheck_4299_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4292_);
                            lean_dec(v___x_4288_);
                            v___x_4294_ = lean_box(0);
                            v_isShared_4295_ = v_isSharedCheck_4299_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_4300_ = lean_array_get_size(v_x_4271_);
                    lean_inc_ref(v_f_4280_);
                    v___x_4301_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_4280_,
                        v___x_4300_,
                        v___y_4282_,
                        v___y_4283_,
                        v___y_4284_,
                        v___y_4285_,
                    );
                    if lean_obj_tag(v___x_4301_) == 0 {
                        v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
                        lean_inc(v_a_4302_);
                        lean_dec_ref_known(v___x_4301_, 1);
                        v_paramInfo_4303_ = lean_ctor_get(v_a_4302_, 0);
                        lean_inc_ref(v_paramInfo_4303_);
                        lean_dec(v_a_4302_);
                        v___x_4304_ = lean_unsigned_to_nat(0);
                        lean_inc_ref(v_post_4267_);
                        lean_inc_ref(v_pre_4266_);
                        v___x_4305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_4300_, v_paramInfo_4303_, v_pre_4266_, v_post_4267_, v_usedLetOnly_4268_, v_skipConstInApp_4269_, v_skipInstances_4265_, v___x_4304_, v_x_4271_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
                        lean_dec_ref(v_paramInfo_4303_);
                        if lean_obj_tag(v___x_4305_) == 0 {
                            v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
                            lean_inc(v_a_4306_);
                            lean_dec_ref_known(v___x_4305_, 1);
                            v___x_4307_ = l_Lean_mkAppN(v_f_4280_, v_a_4306_);
                            lean_dec(v_a_4306_);
                            v___x_4308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4266_, v_post_4267_, v_usedLetOnly_4268_, v_skipConstInApp_4269_, v_skipInstances_4265_, v___x_4307_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
                            return v___x_4308_;
                        } else {
                            lean_dec_ref(v_f_4280_);
                            lean_dec_ref(v_post_4267_);
                            lean_dec_ref(v_pre_4266_);
                            v_a_4309_ = lean_ctor_get(v___x_4305_, 0);
                            v_isSharedCheck_4316_ = (!lean_is_exclusive(v___x_4305_)) as u8;
                            if v_isSharedCheck_4316_ == 0 {
                                v___x_4311_ = v___x_4305_;
                                v_isShared_4312_ = v_isSharedCheck_4316_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4309_);
                                lean_dec(v___x_4305_);
                                v___x_4311_ = lean_box(0);
                                v_isShared_4312_ = v_isSharedCheck_4316_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_f_4280_);
                        lean_dec_ref(v_x_4271_);
                        lean_dec_ref(v_post_4267_);
                        lean_dec_ref(v_pre_4266_);
                        v_a_4317_ = lean_ctor_get(v___x_4301_, 0);
                        v_isSharedCheck_4324_ = (!lean_is_exclusive(v___x_4301_)) as u8;
                        if v_isSharedCheck_4324_ == 0 {
                            v___x_4319_ = v___x_4301_;
                            v_isShared_4320_ = v_isSharedCheck_4324_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4317_);
                            lean_dec(v___x_4301_);
                            v___x_4319_ = lean_box(0);
                            v_isShared_4320_ = v_isSharedCheck_4324_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_4295_ == 0 {
                    v___x_4297_ = v___x_4294_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4297_;
            }
            4 => {
                if v_isShared_4312_ == 0 {
                    v___x_4314_ = v___x_4311_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
                    v___x_4314_ = v_reuseFailAlloc_4315_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4314_;
            }
            6 => {
                if v_isShared_4320_ == 0 {
                    v___x_4322_ = v___x_4319_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
                    v___x_4322_ = v_reuseFailAlloc_4323_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4322_;
            }
            8 => {
                lean_inc_ref(v_post_4267_);
                lean_inc_ref(v_pre_4266_);
                v___x_4326_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4266_, v_post_4267_, v_usedLetOnly_4268_, v_skipConstInApp_4269_, v_skipInstances_4265_, v_x_4270_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
                if lean_obj_tag(v___x_4326_) == 0 {
                    v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
                    lean_inc(v_a_4327_);
                    lean_dec_ref_known(v___x_4326_, 1);
                    v_f_4280_ = v_a_4327_;
                    v___y_4281_ = v___y_4273_;
                    v___y_4282_ = v___y_4274_;
                    v___y_4283_ = v___y_4275_;
                    v___y_4284_ = v___y_4276_;
                    v___y_4285_ = v___y_4277_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_x_4271_);
                    lean_dec_ref(v_post_4267_);
                    lean_dec_ref(v_pre_4266_);
                    return v___x_4326_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(
    mut v___x_4335_: *mut LeanObject,
    mut v_pre_4336_: *mut LeanObject,
    mut v_e_4337_: *mut LeanObject,
    mut v_post_4338_: *mut LeanObject,
    mut v_usedLetOnly_4339_: u8,
    mut v_skipConstInApp_4340_: u8,
    mut v_skipInstances_4341_: u8,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4353_: u8 = 0;
    let mut v___y_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: usize = 0;
    let mut v___x_4373_: usize = 0;
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: usize = 0;
    let mut v___x_4384_: usize = 0;
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_a_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_a_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4348_ = l_Lean_Core_checkSystem(v___x_4335_, v___y_4345_, v___y_4346_);
                if lean_obj_tag(v___x_4348_) == 0 {
                    lean_dec_ref_known(v___x_4348_, 1);
                    lean_inc_ref(v_pre_4336_);
                    lean_inc(v___y_4346_);
                    lean_inc_ref(v___y_4345_);
                    lean_inc(v___y_4344_);
                    lean_inc_ref(v___y_4343_);
                    lean_inc_ref(v_e_4337_);
                    v___x_4349_ = lean_apply_6(
                        v_pre_4336_,
                        v_e_4337_,
                        v___y_4343_,
                        v___y_4344_,
                        v___y_4345_,
                        v___y_4346_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4349_) == 0 {
                        v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
                        v_isSharedCheck_4398_ = (!lean_is_exclusive(v___x_4349_)) as u8;
                        if v_isSharedCheck_4398_ == 0 {
                            v___x_4352_ = v___x_4349_;
                            v_isShared_4353_ = v_isSharedCheck_4398_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4350_);
                            lean_dec(v___x_4349_);
                            v___x_4352_ = lean_box(0);
                            v_isShared_4353_ = v_isSharedCheck_4398_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_post_4338_);
                        lean_dec_ref(v_e_4337_);
                        lean_dec_ref(v_pre_4336_);
                        v_a_4399_ = lean_ctor_get(v___x_4349_, 0);
                        v_isSharedCheck_4406_ = (!lean_is_exclusive(v___x_4349_)) as u8;
                        if v_isSharedCheck_4406_ == 0 {
                            v___x_4401_ = v___x_4349_;
                            v_isShared_4402_ = v_isSharedCheck_4406_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4399_);
                            lean_dec(v___x_4349_);
                            v___x_4401_ = lean_box(0);
                            v_isShared_4402_ = v_isSharedCheck_4406_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_post_4338_);
                    lean_dec_ref(v_e_4337_);
                    lean_dec_ref(v_pre_4336_);
                    v_a_4407_ = lean_ctor_get(v___x_4348_, 0);
                    v_isSharedCheck_4414_ = (!lean_is_exclusive(v___x_4348_)) as u8;
                    if v_isSharedCheck_4414_ == 0 {
                        v___x_4409_ = v___x_4348_;
                        v_isShared_4410_ = v_isSharedCheck_4414_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4407_);
                        lean_dec(v___x_4348_);
                        v___x_4409_ = lean_box(0);
                        v_isShared_4410_ = v_isSharedCheck_4414_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_4350_) {
                0 => {
                    lean_dec_ref(v_post_4338_);
                    lean_dec_ref(v_e_4337_);
                    lean_dec_ref(v_pre_4336_);
                    v_e_4390_ = lean_ctor_get(v_a_4350_, 0);
                    lean_inc_ref(v_e_4390_);
                    lean_dec_ref_known(v_a_4350_, 1);
                    if v_isShared_4353_ == 0 {
                        lean_ctor_set(v___x_4352_, 0, v_e_4390_);
                        v___x_4392_ = v___x_4352_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_e_4390_);
                        v___x_4392_ = v_reuseFailAlloc_4393_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_4352_);
                    lean_dec_ref(v_e_4337_);
                    v_e_4394_ = lean_ctor_get(v_a_4350_, 0);
                    lean_inc_ref(v_e_4394_);
                    lean_dec_ref_known(v_a_4350_, 1);
                    v___x_4395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v_e_4394_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    return v___x_4395_;
                }
                _ => {
                    lean_del_object(v___x_4352_);
                    v_e_x3f_4396_ = lean_ctor_get(v_a_4350_, 0);
                    lean_inc(v_e_x3f_4396_);
                    lean_dec_ref_known(v_a_4350_, 1);
                    if lean_obj_tag(v_e_x3f_4396_) == 0 {
                        v___y_4355_ = v_e_4337_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_e_4337_);
                        v_val_4397_ = lean_ctor_get(v_e_x3f_4396_, 0);
                        lean_inc(v_val_4397_);
                        lean_dec_ref_known(v_e_x3f_4396_, 1);
                        v___y_4355_ = v_val_4397_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match lean_obj_tag(v___y_4355_) {
                7 => {
                    v___x_4356_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0;
                    v___x_4357_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___x_4356_, v___y_4355_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    return v___x_4357_;
                }
                6 => {
                    v___x_4358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0;
                    v___x_4359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___x_4358_, v___y_4355_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    return v___x_4359_;
                }
                8 => {
                    v___x_4360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0;
                    v___x_4361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___x_4360_, v___y_4355_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    return v___x_4361_;
                }
                5 => {
                    v_dummy_4362_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_withAppN___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_withAppN___closed__0_once),
                        _init_l_Lean_Elab_WF_withAppN___closed__0,
                    );
                    v_nargs_4363_ = l_Lean_Expr_getAppNumArgs(v___y_4355_);
                    lean_inc(v_nargs_4363_);
                    v___x_4364_ = lean_mk_array(v_nargs_4363_, v_dummy_4362_);
                    v___x_4365_ = lean_unsigned_to_nat(1);
                    v___x_4366_ = lean_nat_sub(v_nargs_4363_, v___x_4365_);
                    lean_dec(v_nargs_4363_);
                    v___x_4367_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_4341_, v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v___y_4355_, v___x_4364_, v___x_4366_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    return v___x_4367_;
                }
                10 => {
                    v_data_4368_ = lean_ctor_get(v___y_4355_, 0);
                    v_expr_4369_ = lean_ctor_get(v___y_4355_, 1);
                    lean_inc_ref(v_expr_4369_);
                    lean_inc_ref(v_post_4338_);
                    lean_inc_ref(v_pre_4336_);
                    v___x_4370_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v_expr_4369_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    if lean_obj_tag(v___x_4370_) == 0 {
                        v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
                        lean_inc(v_a_4371_);
                        lean_dec_ref_known(v___x_4370_, 1);
                        v___x_4372_ = lean_ptr_addr(v_expr_4369_);
                        v___x_4373_ = lean_ptr_addr(v_a_4371_);
                        v___x_4374_ = lean_usize_dec_eq(v___x_4372_, v___x_4373_);
                        if v___x_4374_ == 0 {
                            lean_inc(v_data_4368_);
                            lean_dec_ref_known(v___y_4355_, 2);
                            v___x_4375_ = l_Lean_Expr_mdata___override(v_data_4368_, v_a_4371_);
                            v___x_4376_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___x_4375_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                            return v___x_4376_;
                        } else {
                            lean_dec(v_a_4371_);
                            v___x_4377_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___y_4355_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                            return v___x_4377_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_4355_, 2);
                        lean_dec_ref(v_post_4338_);
                        lean_dec_ref(v_pre_4336_);
                        return v___x_4370_;
                    }
                }
                11 => {
                    v_typeName_4378_ = lean_ctor_get(v___y_4355_, 0);
                    v_idx_4379_ = lean_ctor_get(v___y_4355_, 1);
                    v_struct_4380_ = lean_ctor_get(v___y_4355_, 2);
                    lean_inc_ref(v_struct_4380_);
                    lean_inc_ref(v_post_4338_);
                    lean_inc_ref(v_pre_4336_);
                    v___x_4381_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v_struct_4380_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    if lean_obj_tag(v___x_4381_) == 0 {
                        v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
                        lean_inc(v_a_4382_);
                        lean_dec_ref_known(v___x_4381_, 1);
                        v___x_4383_ = lean_ptr_addr(v_struct_4380_);
                        v___x_4384_ = lean_ptr_addr(v_a_4382_);
                        v___x_4385_ = lean_usize_dec_eq(v___x_4383_, v___x_4384_);
                        if v___x_4385_ == 0 {
                            lean_inc(v_idx_4379_);
                            lean_inc(v_typeName_4378_);
                            lean_dec_ref_known(v___y_4355_, 3);
                            v___x_4386_ = l_Lean_Expr_proj___override(
                                v_typeName_4378_,
                                v_idx_4379_,
                                v_a_4382_,
                            );
                            v___x_4387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___x_4386_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                            return v___x_4387_;
                        } else {
                            lean_dec(v_a_4382_);
                            v___x_4388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___y_4355_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                            return v___x_4388_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_4355_, 3);
                        lean_dec_ref(v_post_4338_);
                        lean_dec_ref(v_pre_4336_);
                        return v___x_4381_;
                    }
                }
                _ => {
                    v___x_4389_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4336_, v_post_4338_, v_usedLetOnly_4339_, v_skipConstInApp_4340_, v_skipInstances_4341_, v___y_4355_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
                    return v___x_4389_;
                }
            },
            3 => {
                return v___x_4392_;
            }
            4 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4404_;
            }
            6 => {
                if v_isShared_4410_ == 0 {
                    v___x_4412_ = v___x_4409_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
                    v___x_4412_ = v_reuseFailAlloc_4413_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(
    mut v___x_4415_: *mut LeanObject,
    mut v_pre_4416_: *mut LeanObject,
    mut v_e_4417_: *mut LeanObject,
    mut v_post_4418_: *mut LeanObject,
    mut v_usedLetOnly_4419_: *mut LeanObject,
    mut v_skipConstInApp_4420_: *mut LeanObject,
    mut v_skipInstances_4421_: *mut LeanObject,
    mut v___y_4422_: *mut LeanObject,
    mut v___y_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
    mut v___y_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4428_: u8 = 0;
    let mut v_skipConstInApp_boxed_4429_: u8 = 0;
    let mut v_skipInstances_boxed_4430_: u8 = 0;
    let mut v_res_4431_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4428_ = (lean_unbox(v_usedLetOnly_4419_) as u8);
    v_skipConstInApp_boxed_4429_ = (lean_unbox(v_skipConstInApp_4420_) as u8);
    v_skipInstances_boxed_4430_ = (lean_unbox(v_skipInstances_4421_) as u8);
    v_res_4431_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_4415_, v_pre_4416_, v_e_4417_, v_post_4418_, v_usedLetOnly_boxed_4428_, v_skipConstInApp_boxed_4429_, v_skipInstances_boxed_4430_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
    lean_dec(v___y_4426_);
    lean_dec_ref(v___y_4425_);
    lean_dec(v___y_4424_);
    lean_dec_ref(v___y_4423_);
    lean_dec(v___y_4422_);
    return v_res_4431_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(
    mut v_pre_4432_: *mut LeanObject,
    mut v_post_4433_: *mut LeanObject,
    mut v_usedLetOnly_4434_: u8,
    mut v_skipConstInApp_4435_: u8,
    mut v_skipInstances_4436_: u8,
    mut v_e_4437_: *mut LeanObject,
    mut v_a_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_unused_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_val_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut v_a_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_4438_);
                v___x_4444_ =
                    lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___x_4444_, 0, lean_box(0));
                lean_closure_set(v___x_4444_, 1, lean_box(0));
                lean_closure_set(v___x_4444_, 2, v_a_4438_);
                v___x_4445_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_4444_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
                if lean_obj_tag(v___x_4445_) == 0 {
                    v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
                    v_isSharedCheck_4480_ = (!lean_is_exclusive(v___x_4445_)) as u8;
                    if v_isSharedCheck_4480_ == 0 {
                        v___x_4448_ = v___x_4445_;
                        v_isShared_4449_ = v_isSharedCheck_4480_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4446_);
                        lean_dec(v___x_4445_);
                        v___x_4448_ = lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4480_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4437_);
                    lean_dec_ref(v_post_4433_);
                    lean_dec_ref(v_pre_4432_);
                    v_a_4481_ = lean_ctor_get(v___x_4445_, 0);
                    v_isSharedCheck_4488_ = (!lean_is_exclusive(v___x_4445_)) as u8;
                    if v_isSharedCheck_4488_ == 0 {
                        v___x_4483_ = v___x_4445_;
                        v_isShared_4484_ = v_isSharedCheck_4488_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4481_);
                        lean_dec(v___x_4445_);
                        v___x_4483_ = lean_box(0);
                        v_isShared_4484_ = v_isSharedCheck_4488_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_4446_, v_e_4437_);
                lean_dec(v_a_4446_);
                if lean_obj_tag(v___x_4450_) == 0 {
                    lean_del_object(v___x_4448_);
                    v___x_4451_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0;
                    v___x_4452_ = lean_box((v_usedLetOnly_4434_) as usize);
                    v___x_4453_ = lean_box((v_skipConstInApp_4435_) as usize);
                    v___x_4454_ = lean_box((v_skipInstances_4436_) as usize);
                    lean_inc_ref(v_e_4437_);
                    v___f_4455_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed as *mut core::ffi::c_void, 13, 7);
                    lean_closure_set(v___f_4455_, 0, v___x_4451_);
                    lean_closure_set(v___f_4455_, 1, v_pre_4432_);
                    lean_closure_set(v___f_4455_, 2, v_e_4437_);
                    lean_closure_set(v___f_4455_, 3, v_post_4433_);
                    lean_closure_set(v___f_4455_, 4, v___x_4452_);
                    lean_closure_set(v___f_4455_, 5, v___x_4453_);
                    lean_closure_set(v___f_4455_, 6, v___x_4454_);
                    v___x_4456_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_4455_, v_a_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
                    if lean_obj_tag(v___x_4456_) == 0 {
                        v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
                        lean_inc_n(v_a_4457_, 2);
                        lean_dec_ref_known(v___x_4456_, 1);
                        lean_inc(v_a_4438_);
                        v___f_4458_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        lean_closure_set(v___f_4458_, 0, v_a_4438_);
                        lean_closure_set(v___f_4458_, 1, v_e_4437_);
                        lean_closure_set(v___f_4458_, 2, v_a_4457_);
                        v___x_4459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_4458_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
                        if lean_obj_tag(v___x_4459_) == 0 {
                            v_isSharedCheck_4466_ = (!lean_is_exclusive(v___x_4459_)) as u8;
                            if v_isSharedCheck_4466_ == 0 {
                                v_unused_4467_ = lean_ctor_get(v___x_4459_, 0);
                                lean_dec(v_unused_4467_);
                                v___x_4461_ = v___x_4459_;
                                v_isShared_4462_ = v_isSharedCheck_4466_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_4459_);
                                v___x_4461_ = lean_box(0);
                                v_isShared_4462_ = v_isSharedCheck_4466_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4457_);
                            v_a_4468_ = lean_ctor_get(v___x_4459_, 0);
                            v_isSharedCheck_4475_ = (!lean_is_exclusive(v___x_4459_)) as u8;
                            if v_isSharedCheck_4475_ == 0 {
                                v___x_4470_ = v___x_4459_;
                                v_isShared_4471_ = v_isSharedCheck_4475_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4468_);
                                lean_dec(v___x_4459_);
                                v___x_4470_ = lean_box(0);
                                v_isShared_4471_ = v_isSharedCheck_4475_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_4437_);
                        return v___x_4456_;
                    }
                } else {
                    lean_dec_ref(v_e_4437_);
                    lean_dec_ref(v_post_4433_);
                    lean_dec_ref(v_pre_4432_);
                    v_val_4476_ = lean_ctor_get(v___x_4450_, 0);
                    lean_inc(v_val_4476_);
                    lean_dec_ref_known(v___x_4450_, 1);
                    if v_isShared_4449_ == 0 {
                        lean_ctor_set(v___x_4448_, 0, v_val_4476_);
                        v___x_4478_ = v___x_4448_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_val_4476_);
                        v___x_4478_ = v_reuseFailAlloc_4479_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4462_ == 0 {
                    lean_ctor_set(v___x_4461_, 0, v_a_4457_);
                    v___x_4464_ = v___x_4461_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4457_);
                    v___x_4464_ = v_reuseFailAlloc_4465_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4464_;
            }
            4 => {
                if v_isShared_4471_ == 0 {
                    v___x_4473_ = v___x_4470_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4473_;
            }
            6 => {
                return v___x_4478_;
            }
            7 => {
                if v_isShared_4484_ == 0 {
                    v___x_4486_ = v___x_4483_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
                    v___x_4486_ = v_reuseFailAlloc_4487_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(
    mut v_fvars_4489_: *mut LeanObject,
    mut v_pre_4490_: *mut LeanObject,
    mut v_post_4491_: *mut LeanObject,
    mut v_usedLetOnly_4492_: *mut LeanObject,
    mut v_skipConstInApp_4493_: *mut LeanObject,
    mut v_skipInstances_4494_: *mut LeanObject,
    mut v_body_4495_: *mut LeanObject,
    mut v_x_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
    mut v___y_4502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4503_: u8 = 0;
    let mut v_skipConstInApp_boxed_4504_: u8 = 0;
    let mut v_skipInstances_boxed_4505_: u8 = 0;
    let mut v_res_4506_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4503_ = (lean_unbox(v_usedLetOnly_4492_) as u8);
    v_skipConstInApp_boxed_4504_ = (lean_unbox(v_skipConstInApp_4493_) as u8);
    v_skipInstances_boxed_4505_ = (lean_unbox(v_skipInstances_4494_) as u8);
    v_res_4506_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_4489_, v_pre_4490_, v_post_4491_, v_usedLetOnly_boxed_4503_, v_skipConstInApp_boxed_4504_, v_skipInstances_boxed_4505_, v_body_4495_, v_x_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
    lean_dec(v___y_4501_);
    lean_dec_ref(v___y_4500_);
    lean_dec(v___y_4499_);
    lean_dec_ref(v___y_4498_);
    lean_dec(v___y_4497_);
    return v_res_4506_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(
    mut v_pre_4507_: *mut LeanObject,
    mut v_post_4508_: *mut LeanObject,
    mut v_usedLetOnly_4509_: u8,
    mut v_skipConstInApp_4510_: u8,
    mut v_skipInstances_4511_: u8,
    mut v_fvars_4512_: *mut LeanObject,
    mut v_e_4513_: *mut LeanObject,
    mut v_a_4514_: *mut LeanObject,
    mut v___y_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_4513_) == 7 {
        let mut v_binderName_4520_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_4521_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_4522_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_4523_: u8 = 0;
        let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_4520_ = lean_ctor_get(v_e_4513_, 0);
        lean_inc(v_binderName_4520_);
        v_binderType_4521_ = lean_ctor_get(v_e_4513_, 1);
        lean_inc_ref(v_binderType_4521_);
        v_body_4522_ = lean_ctor_get(v_e_4513_, 2);
        lean_inc_ref(v_body_4522_);
        v_binderInfo_4523_ = lean_ctor_get_uint8(
            v_e_4513_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_e_4513_, 3);
        v___x_4524_ = lean_expr_instantiate_rev(v_binderType_4521_, v_fvars_4512_);
        lean_dec_ref(v_binderType_4521_);
        lean_inc_ref(v_post_4508_);
        lean_inc_ref(v_pre_4507_);
        v___x_4525_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4507_, v_post_4508_, v_usedLetOnly_4509_, v_skipConstInApp_4510_, v_skipInstances_4511_, v___x_4524_, v_a_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
        if lean_obj_tag(v___x_4525_) == 0 {
            let mut v_a_4526_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4530_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4531_: u8 = 0;
            let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
            v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
            lean_inc(v_a_4526_);
            lean_dec_ref_known(v___x_4525_, 1);
            v___x_4527_ = lean_box((v_usedLetOnly_4509_) as usize);
            v___x_4528_ = lean_box((v_skipConstInApp_4510_) as usize);
            v___x_4529_ = lean_box((v_skipInstances_4511_) as usize);
            v___f_4530_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            lean_closure_set(v___f_4530_, 0, v_fvars_4512_);
            lean_closure_set(v___f_4530_, 1, v_pre_4507_);
            lean_closure_set(v___f_4530_, 2, v_post_4508_);
            lean_closure_set(v___f_4530_, 3, v___x_4527_);
            lean_closure_set(v___f_4530_, 4, v___x_4528_);
            lean_closure_set(v___f_4530_, 5, v___x_4529_);
            lean_closure_set(v___f_4530_, 6, v_body_4522_);
            v___x_4531_ = 0;
            v___x_4532_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_4520_, v_binderInfo_4523_, v_a_4526_, v___f_4530_, v___x_4531_, v_a_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
            return v___x_4532_;
        } else {
            lean_dec_ref(v_body_4522_);
            lean_dec(v_binderName_4520_);
            lean_dec_ref(v_fvars_4512_);
            lean_dec_ref(v_post_4508_);
            lean_dec_ref(v_pre_4507_);
            return v___x_4525_;
        }
    } else {
        let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
        v___x_4533_ = lean_expr_instantiate_rev(v_e_4513_, v_fvars_4512_);
        lean_dec_ref(v_e_4513_);
        lean_inc_ref(v_post_4508_);
        lean_inc_ref(v_pre_4507_);
        v___x_4534_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4507_, v_post_4508_, v_usedLetOnly_4509_, v_skipConstInApp_4510_, v_skipInstances_4511_, v___x_4533_, v_a_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
        if lean_obj_tag(v___x_4534_) == 0 {
            let mut v_a_4535_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4536_: u8 = 0;
            let mut v___x_4537_: u8 = 0;
            let mut v___x_4538_: u8 = 0;
            let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
            v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
            lean_inc(v_a_4535_);
            lean_dec_ref_known(v___x_4534_, 1);
            v___x_4536_ = 0;
            v___x_4537_ = 1;
            v___x_4538_ = 1;
            v___x_4539_ = l_Lean_Meta_mkForallFVars(
                v_fvars_4512_,
                v_a_4535_,
                v___x_4536_,
                v_usedLetOnly_4509_,
                v___x_4537_,
                v___x_4538_,
                v___y_4515_,
                v___y_4516_,
                v___y_4517_,
                v___y_4518_,
            );
            lean_dec_ref(v_fvars_4512_);
            if lean_obj_tag(v___x_4539_) == 0 {
                let mut v_a_4540_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
                v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
                lean_inc(v_a_4540_);
                lean_dec_ref_known(v___x_4539_, 1);
                v___x_4541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4507_, v_post_4508_, v_usedLetOnly_4509_, v_skipConstInApp_4510_, v_skipInstances_4511_, v_a_4540_, v_a_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
                return v___x_4541_;
            } else {
                lean_dec_ref(v_post_4508_);
                lean_dec_ref(v_pre_4507_);
                return v___x_4539_;
            }
        } else {
            lean_dec_ref(v_fvars_4512_);
            lean_dec_ref(v_post_4508_);
            lean_dec_ref(v_pre_4507_);
            return v___x_4534_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(
    mut v_fvars_4542_: *mut LeanObject,
    mut v_pre_4543_: *mut LeanObject,
    mut v_post_4544_: *mut LeanObject,
    mut v_usedLetOnly_4545_: u8,
    mut v_skipConstInApp_4546_: u8,
    mut v_skipInstances_4547_: u8,
    mut v_body_4548_: *mut LeanObject,
    mut v_x_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
    mut v___y_4554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v___x_4556_ = lean_array_push(v_fvars_4542_, v_x_4549_);
    v___x_4557_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_4543_, v_post_4544_, v_usedLetOnly_4545_, v_skipConstInApp_4546_, v_skipInstances_4547_, v___x_4556_, v_body_4548_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
    return v___x_4557_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(
    mut v_pre_4558_: *mut LeanObject,
    mut v_post_4559_: *mut LeanObject,
    mut v_usedLetOnly_4560_: *mut LeanObject,
    mut v_skipConstInApp_4561_: *mut LeanObject,
    mut v_skipInstances_4562_: *mut LeanObject,
    mut v_e_4563_: *mut LeanObject,
    mut v_a_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
    mut v___y_4569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4570_: u8 = 0;
    let mut v_skipConstInApp_boxed_4571_: u8 = 0;
    let mut v_skipInstances_boxed_4572_: u8 = 0;
    let mut v_res_4573_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4570_ = (lean_unbox(v_usedLetOnly_4560_) as u8);
    v_skipConstInApp_boxed_4571_ = (lean_unbox(v_skipConstInApp_4561_) as u8);
    v_skipInstances_boxed_4572_ = (lean_unbox(v_skipInstances_4562_) as u8);
    v_res_4573_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_4558_, v_post_4559_, v_usedLetOnly_boxed_4570_, v_skipConstInApp_boxed_4571_, v_skipInstances_boxed_4572_, v_e_4563_, v_a_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
    lean_dec(v___y_4568_);
    lean_dec_ref(v___y_4567_);
    lean_dec(v___y_4566_);
    lean_dec_ref(v___y_4565_);
    lean_dec(v_a_4564_);
    return v_res_4573_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(
    mut v_pre_4574_: *mut LeanObject,
    mut v_post_4575_: *mut LeanObject,
    mut v_usedLetOnly_4576_: *mut LeanObject,
    mut v_skipConstInApp_4577_: *mut LeanObject,
    mut v_skipInstances_4578_: *mut LeanObject,
    mut v_sz_4579_: *mut LeanObject,
    mut v_i_4580_: *mut LeanObject,
    mut v_bs_4581_: *mut LeanObject,
    mut v___y_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4588_: u8 = 0;
    let mut v_skipConstInApp_boxed_4589_: u8 = 0;
    let mut v_skipInstances_boxed_4590_: u8 = 0;
    let mut v_sz_boxed_4591_: usize = 0;
    let mut v_i_boxed_4592_: usize = 0;
    let mut v_res_4593_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4588_ = (lean_unbox(v_usedLetOnly_4576_) as u8);
    v_skipConstInApp_boxed_4589_ = (lean_unbox(v_skipConstInApp_4577_) as u8);
    v_skipInstances_boxed_4590_ = (lean_unbox(v_skipInstances_4578_) as u8);
    v_sz_boxed_4591_ = lean_unbox_usize(v_sz_4579_);
    lean_dec(v_sz_4579_);
    v_i_boxed_4592_ = lean_unbox_usize(v_i_4580_);
    lean_dec(v_i_4580_);
    v_res_4593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_4574_, v_post_4575_, v_usedLetOnly_boxed_4588_, v_skipConstInApp_boxed_4589_, v_skipInstances_boxed_4590_, v_sz_boxed_4591_, v_i_boxed_4592_, v_bs_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
    lean_dec(v___y_4586_);
    lean_dec_ref(v___y_4585_);
    lean_dec(v___y_4584_);
    lean_dec_ref(v___y_4583_);
    lean_dec(v___y_4582_);
    return v_res_4593_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(
    mut v_pre_4594_: *mut LeanObject,
    mut v_post_4595_: *mut LeanObject,
    mut v_usedLetOnly_4596_: *mut LeanObject,
    mut v_skipConstInApp_4597_: *mut LeanObject,
    mut v_skipInstances_4598_: *mut LeanObject,
    mut v_e_4599_: *mut LeanObject,
    mut v_a_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4606_: u8 = 0;
    let mut v_skipConstInApp_boxed_4607_: u8 = 0;
    let mut v_skipInstances_boxed_4608_: u8 = 0;
    let mut v_res_4609_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4606_ = (lean_unbox(v_usedLetOnly_4596_) as u8);
    v_skipConstInApp_boxed_4607_ = (lean_unbox(v_skipConstInApp_4597_) as u8);
    v_skipInstances_boxed_4608_ = (lean_unbox(v_skipInstances_4598_) as u8);
    v_res_4609_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4594_, v_post_4595_, v_usedLetOnly_boxed_4606_, v_skipConstInApp_boxed_4607_, v_skipInstances_boxed_4608_, v_e_4599_, v_a_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
    lean_dec(v___y_4604_);
    lean_dec_ref(v___y_4603_);
    lean_dec(v___y_4602_);
    lean_dec_ref(v___y_4601_);
    lean_dec(v_a_4600_);
    return v_res_4609_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(
    mut v_pre_4610_: *mut LeanObject,
    mut v_post_4611_: *mut LeanObject,
    mut v_usedLetOnly_4612_: *mut LeanObject,
    mut v_skipConstInApp_4613_: *mut LeanObject,
    mut v_skipInstances_4614_: *mut LeanObject,
    mut v_fvars_4615_: *mut LeanObject,
    mut v_e_4616_: *mut LeanObject,
    mut v_a_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
    mut v___y_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4623_: u8 = 0;
    let mut v_skipConstInApp_boxed_4624_: u8 = 0;
    let mut v_skipInstances_boxed_4625_: u8 = 0;
    let mut v_res_4626_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4623_ = (lean_unbox(v_usedLetOnly_4612_) as u8);
    v_skipConstInApp_boxed_4624_ = (lean_unbox(v_skipConstInApp_4613_) as u8);
    v_skipInstances_boxed_4625_ = (lean_unbox(v_skipInstances_4614_) as u8);
    v_res_4626_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_4610_, v_post_4611_, v_usedLetOnly_boxed_4623_, v_skipConstInApp_boxed_4624_, v_skipInstances_boxed_4625_, v_fvars_4615_, v_e_4616_, v_a_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
    lean_dec(v___y_4621_);
    lean_dec_ref(v___y_4620_);
    lean_dec(v___y_4619_);
    lean_dec_ref(v___y_4618_);
    lean_dec(v_a_4617_);
    return v_res_4626_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(
    mut v_pre_4627_: *mut LeanObject,
    mut v_post_4628_: *mut LeanObject,
    mut v_usedLetOnly_4629_: *mut LeanObject,
    mut v_skipConstInApp_4630_: *mut LeanObject,
    mut v_skipInstances_4631_: *mut LeanObject,
    mut v_fvars_4632_: *mut LeanObject,
    mut v_e_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4640_: u8 = 0;
    let mut v_skipConstInApp_boxed_4641_: u8 = 0;
    let mut v_skipInstances_boxed_4642_: u8 = 0;
    let mut v_res_4643_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4640_ = (lean_unbox(v_usedLetOnly_4629_) as u8);
    v_skipConstInApp_boxed_4641_ = (lean_unbox(v_skipConstInApp_4630_) as u8);
    v_skipInstances_boxed_4642_ = (lean_unbox(v_skipInstances_4631_) as u8);
    v_res_4643_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_4627_, v_post_4628_, v_usedLetOnly_boxed_4640_, v_skipConstInApp_boxed_4641_, v_skipInstances_boxed_4642_, v_fvars_4632_, v_e_4633_, v_a_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
    lean_dec(v___y_4638_);
    lean_dec_ref(v___y_4637_);
    lean_dec(v___y_4636_);
    lean_dec_ref(v___y_4635_);
    lean_dec(v_a_4634_);
    return v_res_4643_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(
    mut v_pre_4644_: *mut LeanObject,
    mut v_post_4645_: *mut LeanObject,
    mut v_usedLetOnly_4646_: *mut LeanObject,
    mut v_skipConstInApp_4647_: *mut LeanObject,
    mut v_skipInstances_4648_: *mut LeanObject,
    mut v_fvars_4649_: *mut LeanObject,
    mut v_e_4650_: *mut LeanObject,
    mut v_a_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4657_: u8 = 0;
    let mut v_skipConstInApp_boxed_4658_: u8 = 0;
    let mut v_skipInstances_boxed_4659_: u8 = 0;
    let mut v_res_4660_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4657_ = (lean_unbox(v_usedLetOnly_4646_) as u8);
    v_skipConstInApp_boxed_4658_ = (lean_unbox(v_skipConstInApp_4647_) as u8);
    v_skipInstances_boxed_4659_ = (lean_unbox(v_skipInstances_4648_) as u8);
    v_res_4660_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_4644_, v_post_4645_, v_usedLetOnly_boxed_4657_, v_skipConstInApp_boxed_4658_, v_skipInstances_boxed_4659_, v_fvars_4649_, v_e_4650_, v_a_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
    lean_dec(v___y_4655_);
    lean_dec_ref(v___y_4654_);
    lean_dec(v___y_4653_);
    lean_dec_ref(v___y_4652_);
    lean_dec(v_a_4651_);
    return v_res_4660_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(
    mut v_upperBound_4661_: *mut LeanObject,
    mut v___x_4662_: *mut LeanObject,
    mut v_pre_4663_: *mut LeanObject,
    mut v_post_4664_: *mut LeanObject,
    mut v_usedLetOnly_4665_: *mut LeanObject,
    mut v_skipConstInApp_4666_: *mut LeanObject,
    mut v_skipInstances_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
    mut v_b_4669_: *mut LeanObject,
    mut v___y_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4676_: u8 = 0;
    let mut v_skipConstInApp_boxed_4677_: u8 = 0;
    let mut v_skipInstances_boxed_4678_: u8 = 0;
    let mut v_res_4679_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4676_ = (lean_unbox(v_usedLetOnly_4665_) as u8);
    v_skipConstInApp_boxed_4677_ = (lean_unbox(v_skipConstInApp_4666_) as u8);
    v_skipInstances_boxed_4678_ = (lean_unbox(v_skipInstances_4667_) as u8);
    v_res_4679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_4661_, v___x_4662_, v_pre_4663_, v_post_4664_, v_usedLetOnly_boxed_4676_, v_skipConstInApp_boxed_4677_, v_skipInstances_boxed_4678_, v_a_4668_, v_b_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
    lean_dec(v___y_4674_);
    lean_dec_ref(v___y_4673_);
    lean_dec(v___y_4672_);
    lean_dec_ref(v___y_4671_);
    lean_dec(v___y_4670_);
    lean_dec_ref(v___x_4662_);
    lean_dec(v_upperBound_4661_);
    return v_res_4679_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(
    mut v_skipInstances_4680_: *mut LeanObject,
    mut v_pre_4681_: *mut LeanObject,
    mut v_post_4682_: *mut LeanObject,
    mut v_usedLetOnly_4683_: *mut LeanObject,
    mut v_skipConstInApp_4684_: *mut LeanObject,
    mut v_x_4685_: *mut LeanObject,
    mut v_x_4686_: *mut LeanObject,
    mut v_x_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipInstances_boxed_4694_: u8 = 0;
    let mut v_usedLetOnly_boxed_4695_: u8 = 0;
    let mut v_skipConstInApp_boxed_4696_: u8 = 0;
    let mut v_res_4697_: *mut LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_4694_ = (lean_unbox(v_skipInstances_4680_) as u8);
    v_usedLetOnly_boxed_4695_ = (lean_unbox(v_usedLetOnly_4683_) as u8);
    v_skipConstInApp_boxed_4696_ = (lean_unbox(v_skipConstInApp_4684_) as u8);
    v_res_4697_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_4694_, v_pre_4681_, v_post_4682_, v_usedLetOnly_boxed_4695_, v_skipConstInApp_boxed_4696_, v_x_4685_, v_x_4686_, v_x_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
    lean_dec(v___y_4692_);
    lean_dec_ref(v___y_4691_);
    lean_dec(v___y_4690_);
    lean_dec_ref(v___y_4689_);
    lean_dec(v___y_4688_);
    return v_res_4697_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    v___x_4698_ = lean_box(0);
    v___x_4699_ = lean_unsigned_to_nat(16);
    v___x_4700_ = lean_mk_array(v___x_4699_, v___x_4698_);
    return v___x_4700_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    v___x_4701_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0,
    );
    v___x_4702_ = lean_unsigned_to_nat(0);
    v___x_4703_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4703_, 0, v___x_4702_);
    lean_ctor_set(v___x_4703_, 1, v___x_4701_);
    return v___x_4703_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    v___x_4704_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1,
    );
    v___x_4705_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4705_, 0, lean_box(0));
    lean_closure_set(v___x_4705_, 1, lean_box(0));
    lean_closure_set(v___x_4705_, 2, v___x_4704_);
    return v___x_4705_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(
    mut v_input_4706_: *mut LeanObject,
    mut v_pre_4707_: *mut LeanObject,
    mut v_post_4708_: *mut LeanObject,
    mut v_usedLetOnly_4709_: u8,
    mut v_skipConstInApp_4710_: u8,
    mut v___y_4711_: *mut LeanObject,
    mut v___y_4712_: *mut LeanObject,
    mut v___y_4713_: *mut LeanObject,
    mut v___y_4714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4726_: u8 = 0;
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4730_: u8 = 0;
    let mut v_unused_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4716_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once), _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
                v___x_4717_ =
                    l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(
                        lean_box(0),
                        v___x_4716_,
                        v___y_4711_,
                        v___y_4712_,
                        v___y_4713_,
                        v___y_4714_,
                    );
                v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
                lean_inc(v_a_4718_);
                lean_dec_ref(v___x_4717_);
                v___x_4719_ = 0;
                v___x_4720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_4707_, v_post_4708_, v_usedLetOnly_4709_, v_skipConstInApp_4710_, v___x_4719_, v_input_4706_, v_a_4718_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
                if lean_obj_tag(v___x_4720_) == 0 {
                    v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
                    lean_inc(v_a_4721_);
                    lean_dec_ref_known(v___x_4720_, 1);
                    v___x_4722_ = lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___x_4722_, 0, lean_box(0));
                    lean_closure_set(v___x_4722_, 1, lean_box(0));
                    lean_closure_set(v___x_4722_, 2, v_a_4718_);
                    v___x_4723_ =
                        l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(
                            lean_box(0),
                            v___x_4722_,
                            v___y_4711_,
                            v___y_4712_,
                            v___y_4713_,
                            v___y_4714_,
                        );
                    v_isSharedCheck_4730_ = (!lean_is_exclusive(v___x_4723_)) as u8;
                    if v_isSharedCheck_4730_ == 0 {
                        v_unused_4731_ = lean_ctor_get(v___x_4723_, 0);
                        lean_dec(v_unused_4731_);
                        v___x_4725_ = v___x_4723_;
                        v_isShared_4726_ = v_isSharedCheck_4730_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4723_);
                        v___x_4725_ = lean_box(0);
                        v_isShared_4726_ = v_isSharedCheck_4730_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4718_);
                    return v___x_4720_;
                }
            }
            1 => {
                if v_isShared_4726_ == 0 {
                    lean_ctor_set(v___x_4725_, 0, v_a_4721_);
                    v___x_4728_ = v___x_4725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_a_4721_);
                    v___x_4728_ = v_reuseFailAlloc_4729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(
    mut v_input_4732_: *mut LeanObject,
    mut v_pre_4733_: *mut LeanObject,
    mut v_post_4734_: *mut LeanObject,
    mut v_usedLetOnly_4735_: *mut LeanObject,
    mut v_skipConstInApp_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_4742_: u8 = 0;
    let mut v_skipConstInApp_boxed_4743_: u8 = 0;
    let mut v_res_4744_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4742_ = (lean_unbox(v_usedLetOnly_4735_) as u8);
    v_skipConstInApp_boxed_4743_ = (lean_unbox(v_skipConstInApp_4736_) as u8);
    v_res_4744_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(
        v_input_4732_,
        v_pre_4733_,
        v_post_4734_,
        v_usedLetOnly_boxed_4742_,
        v_skipConstInApp_boxed_4743_,
        v___y_4737_,
        v___y_4738_,
        v___y_4739_,
        v___y_4740_,
    );
    lean_dec(v___y_4740_);
    lean_dec_ref(v___y_4739_);
    lean_dec(v___y_4738_);
    lean_dec_ref(v___y_4737_);
    return v_res_4744_;
}
pub unsafe fn _init_l_Lean_Elab_WF_packCalls___closed__2() -> *mut LeanObject {
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    v___x_4747_ = l_Lean_Elab_WF_packCalls___closed__1;
    v___x_4748_ = l_Lean_stringToMessageData(v___x_4747_);
    return v___x_4748_;
}
pub unsafe fn _init_l_Lean_Elab_WF_packCalls___closed__4() -> *mut LeanObject {
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    v___x_4750_ = l_Lean_Elab_WF_packCalls___closed__3;
    v___x_4751_ = l_Lean_stringToMessageData(v___x_4750_);
    return v___x_4751_;
}
pub unsafe fn l_Lean_Elab_WF_packCalls(
    mut v_fixedParamPerms_4752_: *mut LeanObject,
    mut v_argsPacker_4753_: *mut LeanObject,
    mut v_funNames_4754_: *mut LeanObject,
    mut v_newF_4755_: *mut LeanObject,
    mut v_e_4756_: *mut LeanObject,
    mut v_a_4757_: *mut LeanObject,
    mut v_a_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: u8 = 0;
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: u8 = 0;
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4787_: u8 = 0;
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_4760_);
                lean_inc_ref(v_a_4759_);
                lean_inc(v_a_4758_);
                lean_inc_ref(v_a_4757_);
                lean_inc_ref(v_newF_4755_);
                v___x_4762_ =
                    lean_infer_type(v_newF_4755_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
                if lean_obj_tag(v___x_4762_) == 0 {
                    v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
                    lean_inc(v_a_4763_);
                    lean_dec_ref_known(v___x_4762_, 1);
                    v___f_4764_ = l_Lean_Elab_WF_packCalls___closed__0;
                    v___x_4775_ = l_Lean_Expr_isForall(v_a_4763_);
                    if v___x_4775_ == 0 {
                        lean_dec_ref(v_e_4756_);
                        lean_dec_ref(v_funNames_4754_);
                        lean_dec_ref(v_argsPacker_4753_);
                        lean_dec_ref(v_fixedParamPerms_4752_);
                        v___x_4776_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___closed__2_once),
                            _init_l_Lean_Elab_WF_packCalls___closed__2,
                        );
                        v___x_4777_ = l_Lean_MessageData_ofExpr(v_newF_4755_);
                        v___x_4778_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4778_, 0, v___x_4776_);
                        lean_ctor_set(v___x_4778_, 1, v___x_4777_);
                        v___x_4779_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___closed__4_once),
                            _init_l_Lean_Elab_WF_packCalls___closed__4,
                        );
                        v___x_4780_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4780_, 0, v___x_4778_);
                        lean_ctor_set(v___x_4780_, 1, v___x_4779_);
                        v___x_4781_ = l_Lean_MessageData_ofExpr(v_a_4763_);
                        v___x_4782_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4782_, 0, v___x_4780_);
                        lean_ctor_set(v___x_4782_, 1, v___x_4781_);
                        v___x_4783_ =
                            l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(
                                v___x_4782_,
                                v_a_4757_,
                                v_a_4758_,
                                v_a_4759_,
                                v_a_4760_,
                            );
                        v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
                        v_isSharedCheck_4791_ = (!lean_is_exclusive(v___x_4783_)) as u8;
                        if v_isSharedCheck_4791_ == 0 {
                            v___x_4786_ = v___x_4783_;
                            v_isShared_4787_ = v_isSharedCheck_4791_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4784_);
                            lean_dec(v___x_4783_);
                            v___x_4786_ = lean_box(0);
                            v_isShared_4787_ = v_isSharedCheck_4791_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_4766_ = v_a_4757_;
                        v___y_4767_ = v_a_4758_;
                        v___y_4768_ = v_a_4759_;
                        v___y_4769_ = v_a_4760_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4756_);
                    lean_dec_ref(v_newF_4755_);
                    lean_dec_ref(v_funNames_4754_);
                    lean_dec_ref(v_argsPacker_4753_);
                    lean_dec_ref(v_fixedParamPerms_4752_);
                    return v___x_4762_;
                }
            }
            1 => {
                v___x_4770_ = l_Lean_Expr_bindingDomain_x21(v_a_4763_);
                lean_dec(v_a_4763_);
                v___f_4771_ = lean_alloc_closure(
                    l_Lean_Elab_WF_packCalls___lam__2___boxed as *mut core::ffi::c_void,
                    11,
                    5,
                );
                lean_closure_set(v___f_4771_, 0, v_funNames_4754_);
                lean_closure_set(v___f_4771_, 1, v_fixedParamPerms_4752_);
                lean_closure_set(v___f_4771_, 2, v_argsPacker_4753_);
                lean_closure_set(v___f_4771_, 3, v___x_4770_);
                lean_closure_set(v___f_4771_, 4, v_newF_4755_);
                v___x_4772_ = 0;
                v___x_4773_ = 1;
                v___x_4774_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(
                    v_e_4756_,
                    v___f_4764_,
                    v___f_4771_,
                    v___x_4772_,
                    v___x_4773_,
                    v___y_4766_,
                    v___y_4767_,
                    v___y_4768_,
                    v___y_4769_,
                );
                return v___x_4774_;
            }
            2 => {
                if v_isShared_4787_ == 0 {
                    v___x_4789_ = v___x_4786_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
                    v___x_4789_ = v_reuseFailAlloc_4790_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_packCalls___boxed(
    mut v_fixedParamPerms_4792_: *mut LeanObject,
    mut v_argsPacker_4793_: *mut LeanObject,
    mut v_funNames_4794_: *mut LeanObject,
    mut v_newF_4795_: *mut LeanObject,
    mut v_e_4796_: *mut LeanObject,
    mut v_a_4797_: *mut LeanObject,
    mut v_a_4798_: *mut LeanObject,
    mut v_a_4799_: *mut LeanObject,
    mut v_a_4800_: *mut LeanObject,
    mut v_a_4801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4802_: *mut LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Lean_Elab_WF_packCalls(
        v_fixedParamPerms_4792_,
        v_argsPacker_4793_,
        v_funNames_4794_,
        v_newF_4795_,
        v_e_4796_,
        v_a_4797_,
        v_a_4798_,
        v_a_4799_,
        v_a_4800_,
    );
    lean_dec(v_a_4800_);
    lean_dec_ref(v_a_4799_);
    lean_dec(v_a_4798_);
    lean_dec_ref(v_a_4797_);
    return v_res_4802_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(
    mut v_upperBound_4803_: *mut LeanObject,
    mut v___x_4804_: *mut LeanObject,
    mut v_pre_4805_: *mut LeanObject,
    mut v_post_4806_: *mut LeanObject,
    mut v_usedLetOnly_4807_: u8,
    mut v_skipConstInApp_4808_: u8,
    mut v_skipInstances_4809_: u8,
    mut v___x_4810_: *mut LeanObject,
    mut v_inst_4811_: *mut LeanObject,
    mut v_R_4812_: *mut LeanObject,
    mut v_a_4813_: *mut LeanObject,
    mut v_b_4814_: *mut LeanObject,
    mut v_c_4815_: *mut LeanObject,
    mut v___y_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    v___x_4822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_4803_, v___x_4804_, v_pre_4805_, v_post_4806_, v_usedLetOnly_4807_, v_skipConstInApp_4808_, v_skipInstances_4809_, v_a_4813_, v_b_4814_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
    return v___x_4822_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_4823_: *mut LeanObject = *_args.add(0);
    let mut v___x_4824_: *mut LeanObject = *_args.add(1);
    let mut v_pre_4825_: *mut LeanObject = *_args.add(2);
    let mut v_post_4826_: *mut LeanObject = *_args.add(3);
    let mut v_usedLetOnly_4827_: *mut LeanObject = *_args.add(4);
    let mut v_skipConstInApp_4828_: *mut LeanObject = *_args.add(5);
    let mut v_skipInstances_4829_: *mut LeanObject = *_args.add(6);
    let mut v___x_4830_: *mut LeanObject = *_args.add(7);
    let mut v_inst_4831_: *mut LeanObject = *_args.add(8);
    let mut v_R_4832_: *mut LeanObject = *_args.add(9);
    let mut v_a_4833_: *mut LeanObject = *_args.add(10);
    let mut v_b_4834_: *mut LeanObject = *_args.add(11);
    let mut v_c_4835_: *mut LeanObject = *_args.add(12);
    let mut v___y_4836_: *mut LeanObject = *_args.add(13);
    let mut v___y_4837_: *mut LeanObject = *_args.add(14);
    let mut v___y_4838_: *mut LeanObject = *_args.add(15);
    let mut v___y_4839_: *mut LeanObject = *_args.add(16);
    let mut v___y_4840_: *mut LeanObject = *_args.add(17);
    let mut v___y_4841_: *mut LeanObject = *_args.add(18);
    let mut v_usedLetOnly_boxed_4842_: u8 = 0;
    let mut v_skipConstInApp_boxed_4843_: u8 = 0;
    let mut v_skipInstances_boxed_4844_: u8 = 0;
    let mut v_res_4845_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_4842_ = (lean_unbox(v_usedLetOnly_4827_) as u8);
    v_skipConstInApp_boxed_4843_ = (lean_unbox(v_skipConstInApp_4828_) as u8);
    v_skipInstances_boxed_4844_ = (lean_unbox(v_skipInstances_4829_) as u8);
    v_res_4845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_4823_, v___x_4824_, v_pre_4825_, v_post_4826_, v_usedLetOnly_boxed_4842_, v_skipConstInApp_boxed_4843_, v_skipInstances_boxed_4844_, v___x_4830_, v_inst_4831_, v_R_4832_, v_a_4833_, v_b_4834_, v_c_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
    lean_dec(v___y_4840_);
    lean_dec_ref(v___y_4839_);
    lean_dec(v___y_4838_);
    lean_dec_ref(v___y_4837_);
    lean_dec(v___y_4836_);
    lean_dec(v___x_4830_);
    lean_dec_ref(v___x_4824_);
    lean_dec(v_upperBound_4823_);
    return v_res_4845_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(
    mut v_00_u03b2_4846_: *mut LeanObject,
    mut v_m_4847_: *mut LeanObject,
    mut v_a_4848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    v___x_4849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_4847_, v_a_4848_);
    return v___x_4849_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(
    mut v_00_u03b2_4850_: *mut LeanObject,
    mut v_m_4851_: *mut LeanObject,
    mut v_a_4852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4853_: *mut LeanObject = core::ptr::null_mut();
    v_res_4853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_4850_, v_m_4851_, v_a_4852_);
    lean_dec_ref(v_a_4852_);
    lean_dec_ref(v_m_4851_);
    return v_res_4853_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(
    mut v_00_u03b1_4854_: *mut LeanObject,
    mut v_name_4855_: *mut LeanObject,
    mut v_bi_4856_: u8,
    mut v_type_4857_: *mut LeanObject,
    mut v_k_4858_: *mut LeanObject,
    mut v_kind_4859_: u8,
    mut v___y_4860_: *mut LeanObject,
    mut v___y_4861_: *mut LeanObject,
    mut v___y_4862_: *mut LeanObject,
    mut v___y_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    v___x_4866_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_4855_, v_bi_4856_, v_type_4857_, v_k_4858_, v_kind_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
    return v___x_4866_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(
    mut v_00_u03b1_4867_: *mut LeanObject,
    mut v_name_4868_: *mut LeanObject,
    mut v_bi_4869_: *mut LeanObject,
    mut v_type_4870_: *mut LeanObject,
    mut v_k_4871_: *mut LeanObject,
    mut v_kind_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
    mut v___y_4875_: *mut LeanObject,
    mut v___y_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
    mut v___y_4878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4879_: u8 = 0;
    let mut v_kind_boxed_4880_: u8 = 0;
    let mut v_res_4881_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4879_ = (lean_unbox(v_bi_4869_) as u8);
    v_kind_boxed_4880_ = (lean_unbox(v_kind_4872_) as u8);
    v_res_4881_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_4867_, v_name_4868_, v_bi_boxed_4879_, v_type_4870_, v_k_4871_, v_kind_boxed_4880_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
    lean_dec(v___y_4877_);
    lean_dec_ref(v___y_4876_);
    lean_dec(v___y_4875_);
    lean_dec_ref(v___y_4874_);
    lean_dec(v___y_4873_);
    return v_res_4881_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(
    mut v_00_u03b1_4882_: *mut LeanObject,
    mut v_name_4883_: *mut LeanObject,
    mut v_type_4884_: *mut LeanObject,
    mut v_val_4885_: *mut LeanObject,
    mut v_k_4886_: *mut LeanObject,
    mut v_nondep_4887_: u8,
    mut v_kind_4888_: u8,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
    mut v___y_4892_: *mut LeanObject,
    mut v___y_4893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    v___x_4895_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_4883_, v_type_4884_, v_val_4885_, v_k_4886_, v_nondep_4887_, v_kind_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
    return v___x_4895_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(
    mut v_00_u03b1_4896_: *mut LeanObject,
    mut v_name_4897_: *mut LeanObject,
    mut v_type_4898_: *mut LeanObject,
    mut v_val_4899_: *mut LeanObject,
    mut v_k_4900_: *mut LeanObject,
    mut v_nondep_4901_: *mut LeanObject,
    mut v_kind_4902_: *mut LeanObject,
    mut v___y_4903_: *mut LeanObject,
    mut v___y_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
    mut v___y_4906_: *mut LeanObject,
    mut v___y_4907_: *mut LeanObject,
    mut v___y_4908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_4909_: u8 = 0;
    let mut v_kind_boxed_4910_: u8 = 0;
    let mut v_res_4911_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4909_ = (lean_unbox(v_nondep_4901_) as u8);
    v_kind_boxed_4910_ = (lean_unbox(v_kind_4902_) as u8);
    v_res_4911_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_4896_, v_name_4897_, v_type_4898_, v_val_4899_, v_k_4900_, v_nondep_boxed_4909_, v_kind_boxed_4910_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
    lean_dec(v___y_4907_);
    lean_dec_ref(v___y_4906_);
    lean_dec(v___y_4905_);
    lean_dec_ref(v___y_4904_);
    lean_dec(v___y_4903_);
    return v_res_4911_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(
    mut v_00_u03b1_4912_: *mut LeanObject,
    mut v_ref_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
    mut v___y_4915_: *mut LeanObject,
    mut v___y_4916_: *mut LeanObject,
    mut v___y_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    v___x_4919_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_4913_);
    return v___x_4919_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(
    mut v_00_u03b1_4920_: *mut LeanObject,
    mut v_ref_4921_: *mut LeanObject,
    mut v___y_4922_: *mut LeanObject,
    mut v___y_4923_: *mut LeanObject,
    mut v___y_4924_: *mut LeanObject,
    mut v___y_4925_: *mut LeanObject,
    mut v___y_4926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4927_: *mut LeanObject = core::ptr::null_mut();
    v_res_4927_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_4920_, v_ref_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
    lean_dec(v___y_4925_);
    lean_dec_ref(v___y_4924_);
    lean_dec(v___y_4923_);
    lean_dec_ref(v___y_4922_);
    return v_res_4927_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(
    mut v_00_u03b1_4928_: *mut LeanObject,
    mut v_x_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
    mut v___y_4931_: *mut LeanObject,
    mut v___y_4932_: *mut LeanObject,
    mut v___y_4933_: *mut LeanObject,
    mut v___y_4934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    v___x_4936_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
    return v___x_4936_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(
    mut v_00_u03b1_4937_: *mut LeanObject,
    mut v_x_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4945_: *mut LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_4937_, v_x_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
    lean_dec(v___y_4943_);
    lean_dec_ref(v___y_4942_);
    lean_dec(v___y_4941_);
    lean_dec_ref(v___y_4940_);
    lean_dec(v___y_4939_);
    return v_res_4945_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(
    mut v_00_u03b2_4946_: *mut LeanObject,
    mut v_m_4947_: *mut LeanObject,
    mut v_a_4948_: *mut LeanObject,
    mut v_b_4949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_4947_, v_a_4948_, v_b_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(
    mut v_00_u03b2_4951_: *mut LeanObject,
    mut v_a_4952_: *mut LeanObject,
    mut v_x_4953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    v___x_4954_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_4952_, v_x_4953_);
    return v___x_4954_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(
    mut v_00_u03b2_4955_: *mut LeanObject,
    mut v_a_4956_: *mut LeanObject,
    mut v_x_4957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4958_: *mut LeanObject = core::ptr::null_mut();
    v_res_4958_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_4955_, v_a_4956_, v_x_4957_);
    lean_dec(v_x_4957_);
    lean_dec_ref(v_a_4956_);
    return v_res_4958_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(
    mut v_00_u03b2_4959_: *mut LeanObject,
    mut v_a_4960_: *mut LeanObject,
    mut v_x_4961_: *mut LeanObject,
) -> u8 {
    let mut v___x_4962_: u8 = 0;
    v___x_4962_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_4960_, v_x_4961_);
    return v___x_4962_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(
    mut v_00_u03b2_4963_: *mut LeanObject,
    mut v_a_4964_: *mut LeanObject,
    mut v_x_4965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4966_: u8 = 0;
    let mut v_r_4967_: *mut LeanObject = core::ptr::null_mut();
    v_res_4966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_4963_, v_a_4964_, v_x_4965_);
    lean_dec(v_x_4965_);
    lean_dec_ref(v_a_4964_);
    v_r_4967_ = lean_box((v_res_4966_) as usize);
    return v_r_4967_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(
    mut v_00_u03b2_4968_: *mut LeanObject,
    mut v_data_4969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    v___x_4970_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_4969_);
    return v___x_4970_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(
    mut v_00_u03b2_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
    mut v_b_4973_: *mut LeanObject,
    mut v_x_4974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    v___x_4975_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_4972_, v_b_4973_, v_x_4974_);
    return v___x_4975_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(
    mut v_00_u03b2_4976_: *mut LeanObject,
    mut v_i_4977_: *mut LeanObject,
    mut v_source_4978_: *mut LeanObject,
    mut v_target_4979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    v___x_4980_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_4977_, v_source_4978_, v_target_4979_);
    return v___x_4980_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(
    mut v_00_u03b2_4981_: *mut LeanObject,
    mut v_x_4982_: *mut LeanObject,
    mut v_x_4983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    v___x_4984_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_4982_, v_x_4983_);
    return v___x_4984_;
}
pub unsafe fn l_Lean_Elab_WF_mutualName(
    mut v_fixedParamPerms_4991_: *mut LeanObject,
    mut v_argsPacker_4992_: *mut LeanObject,
    mut v_preDefs_4993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4995_: u8 = 0;
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: u8 = 0;
    let mut v___x_5016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5015_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_4991_);
                if v___x_5015_ == 0 {
                    v___y_4995_ = v___x_5015_;
                    state = 1;
                    continue;
                } else {
                    v___x_5016_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_4992_);
                    v___y_4995_ = v___x_5016_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4995_ == 0 {
                    v___x_4996_ = lean_unsigned_to_nat(1);
                    v___x_4997_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_4992_);
                    v___x_4998_ = lean_nat_dec_lt(v___x_4996_, v___x_4997_);
                    lean_dec(v___x_4997_);
                    if v___x_4998_ == 0 {
                        v___x_4999_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                        v___x_5000_ = lean_unsigned_to_nat(0);
                        v___x_5001_ =
                            lean_array_get_borrowed(v___x_4999_, v_preDefs_4993_, v___x_5000_);
                        v_declName_5002_ = lean_ctor_get(v___x_5001_, 3);
                        v___x_5003_ = l_Lean_Elab_WF_mutualName___closed__1;
                        lean_inc(v_declName_5002_);
                        v___x_5004_ = l_Lean_Name_append(v_declName_5002_, v___x_5003_);
                        return v___x_5004_;
                    } else {
                        v___x_5005_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                        v___x_5006_ = lean_unsigned_to_nat(0);
                        v___x_5007_ =
                            lean_array_get_borrowed(v___x_5005_, v_preDefs_4993_, v___x_5006_);
                        v_declName_5008_ = lean_ctor_get(v___x_5007_, 3);
                        v___x_5009_ = l_Lean_Elab_WF_mutualName___closed__3;
                        lean_inc(v_declName_5008_);
                        v___x_5010_ = l_Lean_Name_append(v_declName_5008_, v___x_5009_);
                        return v___x_5010_;
                    }
                } else {
                    v___x_5011_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                    v___x_5012_ = lean_unsigned_to_nat(0);
                    v___x_5013_ =
                        lean_array_get_borrowed(v___x_5011_, v_preDefs_4993_, v___x_5012_);
                    v_declName_5014_ = lean_ctor_get(v___x_5013_, 3);
                    lean_inc(v_declName_5014_);
                    return v_declName_5014_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_mutualName___boxed(
    mut v_fixedParamPerms_5017_: *mut LeanObject,
    mut v_argsPacker_5018_: *mut LeanObject,
    mut v_preDefs_5019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5020_: *mut LeanObject = core::ptr::null_mut();
    v_res_5020_ =
        l_Lean_Elab_WF_mutualName(v_fixedParamPerms_5017_, v_argsPacker_5018_, v_preDefs_5019_);
    lean_dec_ref(v_preDefs_5019_);
    lean_dec_ref(v_argsPacker_5018_);
    return v_res_5020_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(
    mut v_k_5021_: *mut LeanObject,
    mut v_b_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5026_);
    lean_inc_ref(v___y_5025_);
    lean_inc(v___y_5024_);
    lean_inc_ref(v___y_5023_);
    v___x_5028_ = lean_apply_6(
        v_k_5021_,
        v_b_5022_,
        v___y_5023_,
        v___y_5024_,
        v___y_5025_,
        v___y_5026_,
        lean_box(0),
    );
    return v___x_5028_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(
    mut v_k_5029_: *mut LeanObject,
    mut v_b_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5036_: *mut LeanObject = core::ptr::null_mut();
    v_res_5036_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_5029_, v_b_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
    lean_dec(v___y_5034_);
    lean_dec_ref(v___y_5033_);
    lean_dec(v___y_5032_);
    lean_dec_ref(v___y_5031_);
    return v_res_5036_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(
    mut v_perm_5037_: *mut LeanObject,
    mut v_type_5038_: *mut LeanObject,
    mut v_k_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
    mut v___y_5043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5050_: u8 = 0;
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5054_: u8 = 0;
    let mut v_a_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5058_: u8 = 0;
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5045_ = lean_alloc_closure(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_5045_, 0, v_k_5039_);
                v___x_5046_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_5037_, v_type_5038_, v___f_5045_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
                if lean_obj_tag(v___x_5046_) == 0 {
                    v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
                    v_isSharedCheck_5054_ = (!lean_is_exclusive(v___x_5046_)) as u8;
                    if v_isSharedCheck_5054_ == 0 {
                        v___x_5049_ = v___x_5046_;
                        v_isShared_5050_ = v_isSharedCheck_5054_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5047_);
                        lean_dec(v___x_5046_);
                        v___x_5049_ = lean_box(0);
                        v_isShared_5050_ = v_isSharedCheck_5054_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5055_ = lean_ctor_get(v___x_5046_, 0);
                    v_isSharedCheck_5062_ = (!lean_is_exclusive(v___x_5046_)) as u8;
                    if v_isSharedCheck_5062_ == 0 {
                        v___x_5057_ = v___x_5046_;
                        v_isShared_5058_ = v_isSharedCheck_5062_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5055_);
                        lean_dec(v___x_5046_);
                        v___x_5057_ = lean_box(0);
                        v_isShared_5058_ = v_isSharedCheck_5062_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5050_ == 0 {
                    v___x_5052_ = v___x_5049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
                    v___x_5052_ = v_reuseFailAlloc_5053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5052_;
            }
            3 => {
                if v_isShared_5058_ == 0 {
                    v___x_5060_ = v___x_5057_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5061_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5055_);
                    v___x_5060_ = v_reuseFailAlloc_5061_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(
    mut v_perm_5063_: *mut LeanObject,
    mut v_type_5064_: *mut LeanObject,
    mut v_k_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5071_: *mut LeanObject = core::ptr::null_mut();
    v_res_5071_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_5063_, v_type_5064_, v_k_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
    lean_dec(v___y_5069_);
    lean_dec_ref(v___y_5068_);
    lean_dec(v___y_5067_);
    lean_dec_ref(v___y_5066_);
    return v_res_5071_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(
    mut v_00_u03b1_5072_: *mut LeanObject,
    mut v_perm_5073_: *mut LeanObject,
    mut v_type_5074_: *mut LeanObject,
    mut v_k_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    v___x_5081_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_5073_, v_type_5074_, v_k_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
    return v___x_5081_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(
    mut v_00_u03b1_5082_: *mut LeanObject,
    mut v_perm_5083_: *mut LeanObject,
    mut v_type_5084_: *mut LeanObject,
    mut v_k_5085_: *mut LeanObject,
    mut v___y_5086_: *mut LeanObject,
    mut v___y_5087_: *mut LeanObject,
    mut v___y_5088_: *mut LeanObject,
    mut v___y_5089_: *mut LeanObject,
    mut v___y_5090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5091_: *mut LeanObject = core::ptr::null_mut();
    v_res_5091_ =
        l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(
            v_00_u03b1_5082_,
            v_perm_5083_,
            v_type_5084_,
            v_k_5085_,
            v___y_5086_,
            v___y_5087_,
            v___y_5088_,
            v___y_5089_,
        );
    lean_dec(v___y_5089_);
    lean_dec_ref(v___y_5088_);
    lean_dec(v___y_5087_);
    lean_dec_ref(v___y_5086_);
    return v_res_5091_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(
    mut v___x_5092_: *mut LeanObject,
    mut v_ys_5093_: *mut LeanObject,
    mut v_as_5094_: *mut LeanObject,
    mut v_i_5095_: *mut LeanObject,
    mut v_j_5096_: *mut LeanObject,
    mut v_bs_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5104_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5103_ = lean_unsigned_to_nat(0);
                v_isZero_5104_ = lean_nat_dec_eq(v_i_5095_, v_zero_5103_);
                if v_isZero_5104_ == 1 {
                    lean_dec(v_j_5096_);
                    lean_dec(v_i_5095_);
                    lean_dec_ref(v_ys_5093_);
                    v___x_5105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5105_, 0, v_bs_5097_);
                    return v___x_5105_;
                } else {
                    v___x_5106_ = lean_array_fget_borrowed(v_as_5094_, v_j_5096_);
                    v_value_5107_ = lean_ctor_get(v___x_5106_, 7);
                    v___x_5108_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4_once),
                        _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4,
                    );
                    v___x_5109_ = lean_array_get_borrowed(v___x_5108_, v___x_5092_, v_j_5096_);
                    lean_inc_ref(v_ys_5093_);
                    lean_inc_ref(v_value_5107_);
                    lean_inc(v___x_5109_);
                    v___x_5110_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(
                        v___x_5109_,
                        v_value_5107_,
                        v_ys_5093_,
                        v___y_5098_,
                        v___y_5099_,
                        v___y_5100_,
                        v___y_5101_,
                    );
                    if lean_obj_tag(v___x_5110_) == 0 {
                        v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
                        lean_inc(v_a_5111_);
                        lean_dec_ref_known(v___x_5110_, 1);
                        v_one_5112_ = lean_unsigned_to_nat(1);
                        v_n_5113_ = lean_nat_sub(v_i_5095_, v_one_5112_);
                        lean_dec(v_i_5095_);
                        v___x_5114_ = lean_nat_add(v_j_5096_, v_one_5112_);
                        lean_dec(v_j_5096_);
                        v___x_5115_ = lean_array_push(v_bs_5097_, v_a_5111_);
                        v_i_5095_ = v_n_5113_;
                        v_j_5096_ = v___x_5114_;
                        v_bs_5097_ = v___x_5115_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5097_);
                        lean_dec(v_j_5096_);
                        lean_dec(v_i_5095_);
                        lean_dec_ref(v_ys_5093_);
                        v_a_5117_ = lean_ctor_get(v___x_5110_, 0);
                        v_isSharedCheck_5124_ = (!lean_is_exclusive(v___x_5110_)) as u8;
                        if v_isSharedCheck_5124_ == 0 {
                            v___x_5119_ = v___x_5110_;
                            v_isShared_5120_ = v_isSharedCheck_5124_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5117_);
                            lean_dec(v___x_5110_);
                            v___x_5119_ = lean_box(0);
                            v_isShared_5120_ = v_isSharedCheck_5124_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5120_ == 0 {
                    v___x_5122_ = v___x_5119_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
                    v___x_5122_ = v_reuseFailAlloc_5123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(
    mut v___x_5125_: *mut LeanObject,
    mut v_ys_5126_: *mut LeanObject,
    mut v_as_5127_: *mut LeanObject,
    mut v_i_5128_: *mut LeanObject,
    mut v_j_5129_: *mut LeanObject,
    mut v_bs_5130_: *mut LeanObject,
    mut v___y_5131_: *mut LeanObject,
    mut v___y_5132_: *mut LeanObject,
    mut v___y_5133_: *mut LeanObject,
    mut v___y_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5136_: *mut LeanObject = core::ptr::null_mut();
    v_res_5136_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(
        v___x_5125_,
        v_ys_5126_,
        v_as_5127_,
        v_i_5128_,
        v_j_5129_,
        v_bs_5130_,
        v___y_5131_,
        v___y_5132_,
        v___y_5133_,
        v___y_5134_,
    );
    lean_dec(v___y_5134_);
    lean_dec_ref(v___y_5133_);
    lean_dec(v___y_5132_);
    lean_dec_ref(v___y_5131_);
    lean_dec_ref(v_as_5127_);
    lean_dec_ref(v___x_5125_);
    return v_res_5136_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(
    mut v___x_5137_: *mut LeanObject,
    mut v_ys_5138_: *mut LeanObject,
    mut v_as_5139_: *mut LeanObject,
    mut v_i_5140_: *mut LeanObject,
    mut v_j_5141_: *mut LeanObject,
    mut v_bs_5142_: *mut LeanObject,
    mut v___y_5143_: *mut LeanObject,
    mut v___y_5144_: *mut LeanObject,
    mut v___y_5145_: *mut LeanObject,
    mut v___y_5146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5149_: u8 = 0;
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5148_ = lean_unsigned_to_nat(0);
                v_isZero_5149_ = lean_nat_dec_eq(v_i_5140_, v_zero_5148_);
                if v_isZero_5149_ == 1 {
                    lean_dec(v_j_5141_);
                    lean_dec(v_i_5140_);
                    lean_dec_ref(v_ys_5138_);
                    v___x_5150_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5150_, 0, v_bs_5142_);
                    return v___x_5150_;
                } else {
                    v___x_5151_ = lean_array_fget_borrowed(v_as_5139_, v_j_5141_);
                    v_type_5152_ = lean_ctor_get(v___x_5151_, 6);
                    v___x_5153_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4_once),
                        _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4,
                    );
                    v___x_5154_ = lean_array_get_borrowed(v___x_5153_, v___x_5137_, v_j_5141_);
                    lean_inc_ref(v_ys_5138_);
                    lean_inc_ref(v_type_5152_);
                    lean_inc(v___x_5154_);
                    v___x_5155_ = l_Lean_Elab_FixedParamPerm_instantiateForall(
                        v___x_5154_,
                        v_type_5152_,
                        v_ys_5138_,
                        v___y_5143_,
                        v___y_5144_,
                        v___y_5145_,
                        v___y_5146_,
                    );
                    if lean_obj_tag(v___x_5155_) == 0 {
                        v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
                        lean_inc(v_a_5156_);
                        lean_dec_ref_known(v___x_5155_, 1);
                        v_one_5157_ = lean_unsigned_to_nat(1);
                        v_n_5158_ = lean_nat_sub(v_i_5140_, v_one_5157_);
                        lean_dec(v_i_5140_);
                        v___x_5159_ = lean_nat_add(v_j_5141_, v_one_5157_);
                        lean_dec(v_j_5141_);
                        v___x_5160_ = lean_array_push(v_bs_5142_, v_a_5156_);
                        v_i_5140_ = v_n_5158_;
                        v_j_5141_ = v___x_5159_;
                        v_bs_5142_ = v___x_5160_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5142_);
                        lean_dec(v_j_5141_);
                        lean_dec(v_i_5140_);
                        lean_dec_ref(v_ys_5138_);
                        v_a_5162_ = lean_ctor_get(v___x_5155_, 0);
                        v_isSharedCheck_5169_ = (!lean_is_exclusive(v___x_5155_)) as u8;
                        if v_isSharedCheck_5169_ == 0 {
                            v___x_5164_ = v___x_5155_;
                            v_isShared_5165_ = v_isSharedCheck_5169_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5162_);
                            lean_dec(v___x_5155_);
                            v___x_5164_ = lean_box(0);
                            v_isShared_5165_ = v_isSharedCheck_5169_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5165_ == 0 {
                    v___x_5167_ = v___x_5164_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5168_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
                    v___x_5167_ = v_reuseFailAlloc_5168_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(
    mut v___x_5170_: *mut LeanObject,
    mut v_ys_5171_: *mut LeanObject,
    mut v_as_5172_: *mut LeanObject,
    mut v_i_5173_: *mut LeanObject,
    mut v_j_5174_: *mut LeanObject,
    mut v_bs_5175_: *mut LeanObject,
    mut v___y_5176_: *mut LeanObject,
    mut v___y_5177_: *mut LeanObject,
    mut v___y_5178_: *mut LeanObject,
    mut v___y_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5181_: *mut LeanObject = core::ptr::null_mut();
    v_res_5181_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(
        v___x_5170_,
        v_ys_5171_,
        v_as_5172_,
        v_i_5173_,
        v_j_5174_,
        v_bs_5175_,
        v___y_5176_,
        v___y_5177_,
        v___y_5178_,
        v___y_5179_,
    );
    lean_dec(v___y_5179_);
    lean_dec_ref(v___y_5178_);
    lean_dec(v___y_5177_);
    lean_dec_ref(v___y_5176_);
    lean_dec_ref(v_as_5172_);
    lean_dec_ref(v___x_5170_);
    return v_res_5181_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(
    mut v_a_5182_: *mut LeanObject,
    mut v_a_5183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5189_: u8 = 0;
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5182_) == 0 {
                    v___x_5184_ = l_List_reverse___redArg(v_a_5183_);
                    return v___x_5184_;
                } else {
                    v_head_5185_ = lean_ctor_get(v_a_5182_, 0);
                    v_tail_5186_ = lean_ctor_get(v_a_5182_, 1);
                    v_isSharedCheck_5195_ = (!lean_is_exclusive(v_a_5182_)) as u8;
                    if v_isSharedCheck_5195_ == 0 {
                        v___x_5188_ = v_a_5182_;
                        v_isShared_5189_ = v_isSharedCheck_5195_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5186_);
                        lean_inc(v_head_5185_);
                        lean_dec(v_a_5182_);
                        v___x_5188_ = lean_box(0);
                        v_isShared_5189_ = v_isSharedCheck_5195_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5190_ = l_Lean_mkLevelParam(v_head_5185_);
                if v_isShared_5189_ == 0 {
                    lean_ctor_set(v___x_5188_, 1, v_a_5183_);
                    lean_ctor_set(v___x_5188_, 0, v___x_5190_);
                    v___x_5192_ = v___x_5188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5194_, 0, v___x_5190_);
                    lean_ctor_set(v_reuseFailAlloc_5194_, 1, v_a_5183_);
                    v___x_5192_ = v_reuseFailAlloc_5194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5182_ = v_tail_5186_;
                v_a_5183_ = v___x_5192_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(
    mut v_sz_5196_: usize,
    mut v_i_5197_: usize,
    mut v_bs_5198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5199_: u8 = 0;
    let mut v_v_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: usize = 0;
    let mut v___x_5205_: usize = 0;
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5199_ = lean_usize_dec_lt(v_i_5197_, v_sz_5196_);
                if v___x_5199_ == 0 {
                    return v_bs_5198_;
                } else {
                    v_v_5200_ = lean_array_uget_borrowed(v_bs_5198_, v_i_5197_);
                    v_declName_5201_ = lean_ctor_get(v_v_5200_, 3);
                    lean_inc(v_declName_5201_);
                    v___x_5202_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5203_ = lean_array_uset(v_bs_5198_, v_i_5197_, v___x_5202_);
                    v___x_5204_ = 1usize;
                    v___x_5205_ = lean_usize_add(v_i_5197_, v___x_5204_);
                    v___x_5206_ = lean_array_uset(v_bs_x27_5203_, v_i_5197_, v_declName_5201_);
                    v_i_5197_ = v___x_5205_;
                    v_bs_5198_ = v___x_5206_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(
    mut v_sz_5208_: *mut LeanObject,
    mut v_i_5209_: *mut LeanObject,
    mut v_bs_5210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5211_: usize = 0;
    let mut v_i_boxed_5212_: usize = 0;
    let mut v_res_5213_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5211_ = lean_unbox_usize(v_sz_5208_);
    lean_dec(v_sz_5208_);
    v_i_boxed_5212_ = lean_unbox_usize(v_i_5209_);
    lean_dec(v_i_5209_);
    v_res_5213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_5211_, v_i_boxed_5212_, v_bs_5210_);
    return v_res_5213_;
}
pub unsafe fn l_Lean_Elab_WF_packMutual___lam__0(
    mut v_preDefs_5214_: *mut LeanObject,
    mut v_perms_5215_: *mut LeanObject,
    mut v___x_5216_: *mut LeanObject,
    mut v_argsPacker_5217_: *mut LeanObject,
    mut v___x_5218_: u8,
    mut v_ref_5219_: *mut LeanObject,
    mut v_kind_5220_: u8,
    mut v_levelParams_5221_: *mut LeanObject,
    mut v_modifiers_5222_: *mut LeanObject,
    mut v_newFn_5223_: *mut LeanObject,
    mut v_binders_5224_: *mut LeanObject,
    mut v_numSectionVars_5225_: *mut LeanObject,
    mut v_value_5226_: *mut LeanObject,
    mut v_termination_5227_: *mut LeanObject,
    mut v_fixedParamPerms_5228_: *mut LeanObject,
    mut v_ys_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
    mut v___y_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: u8 = 0;
    let mut v___x_5244_: u8 = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5255_: usize = 0;
    let mut v___x_5256_: usize = 0;
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5264_: u8 = 0;
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5269_: u8 = 0;
    let mut v_a_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5273_: u8 = 0;
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5277_: u8 = 0;
    let mut v_a_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5281_: u8 = 0;
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5285_: u8 = 0;
    let mut v_a_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5293_: u8 = 0;
    let mut v_a_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut v_a_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5305_: u8 = 0;
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5309_: u8 = 0;
    let mut v_a_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5313_: u8 = 0;
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_a_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v_a_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = lean_array_get_size(v_preDefs_5214_);
                v___x_5236_ = lean_mk_empty_array_with_capacity(v___x_5235_);
                lean_inc_ref(v___x_5236_);
                lean_inc(v___x_5216_);
                lean_inc_ref(v_ys_5229_);
                v___x_5237_ =
                    l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(
                        v_perms_5215_,
                        v_ys_5229_,
                        v_preDefs_5214_,
                        v___x_5235_,
                        v___x_5216_,
                        v___x_5236_,
                        v___y_5230_,
                        v___y_5231_,
                        v___y_5232_,
                        v___y_5233_,
                    );
                if lean_obj_tag(v___x_5237_) == 0 {
                    v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
                    lean_inc(v_a_5238_);
                    lean_dec_ref_known(v___x_5237_, 1);
                    lean_inc_ref(v_ys_5229_);
                    v___x_5239_ =
                        l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(
                            v_perms_5215_,
                            v_ys_5229_,
                            v_preDefs_5214_,
                            v___x_5235_,
                            v___x_5216_,
                            v___x_5236_,
                            v___y_5230_,
                            v___y_5231_,
                            v___y_5232_,
                            v___y_5233_,
                        );
                    if lean_obj_tag(v___x_5239_) == 0 {
                        v_a_5240_ = lean_ctor_get(v___x_5239_, 0);
                        lean_inc(v_a_5240_);
                        lean_dec_ref_known(v___x_5239_, 1);
                        v___x_5241_ = l_Lean_Meta_ArgsPacker_uncurryType(
                            v_argsPacker_5217_,
                            v_a_5238_,
                            v___y_5230_,
                            v___y_5231_,
                            v___y_5232_,
                            v___y_5233_,
                        );
                        lean_dec(v_a_5238_);
                        if lean_obj_tag(v___x_5241_) == 0 {
                            v_a_5242_ = lean_ctor_get(v___x_5241_, 0);
                            lean_inc(v_a_5242_);
                            lean_dec_ref_known(v___x_5241_, 1);
                            v___x_5243_ = 1;
                            v___x_5244_ = 1;
                            v___x_5245_ = l_Lean_Meta_mkForallFVars(
                                v_ys_5229_,
                                v_a_5242_,
                                v___x_5218_,
                                v___x_5243_,
                                v___x_5243_,
                                v___x_5244_,
                                v___y_5230_,
                                v___y_5231_,
                                v___y_5232_,
                                v___y_5233_,
                            );
                            if lean_obj_tag(v___x_5245_) == 0 {
                                v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
                                lean_inc_n(v_a_5246_, 2);
                                lean_dec_ref_known(v___x_5245_, 1);
                                lean_inc_ref(v_termination_5227_);
                                lean_inc(v_numSectionVars_5225_);
                                lean_inc(v_binders_5224_);
                                lean_inc(v_newFn_5223_);
                                lean_inc_ref(v_modifiers_5222_);
                                lean_inc(v_levelParams_5221_);
                                lean_inc(v_ref_5219_);
                                v___x_5247_ = lean_alloc_ctor(0, 9, (1) as u32);
                                lean_ctor_set(v___x_5247_, 0, v_ref_5219_);
                                lean_ctor_set(v___x_5247_, 1, v_levelParams_5221_);
                                lean_ctor_set(v___x_5247_, 2, v_modifiers_5222_);
                                lean_ctor_set(v___x_5247_, 3, v_newFn_5223_);
                                lean_ctor_set(v___x_5247_, 4, v_binders_5224_);
                                lean_ctor_set(v___x_5247_, 5, v_numSectionVars_5225_);
                                lean_ctor_set(v___x_5247_, 6, v_a_5246_);
                                lean_ctor_set(v___x_5247_, 7, v_value_5226_);
                                lean_ctor_set(v___x_5247_, 8, v_termination_5227_);
                                lean_ctor_set_uint8(
                                    v___x_5247_,
                                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                                    v_kind_5220_,
                                );
                                v___x_5248_ = l_Lean_Elab_addAsAxiom___redArg(
                                    v___x_5247_,
                                    v___y_5232_,
                                    v___y_5233_,
                                );
                                lean_dec_ref_known(v___x_5247_, 9);
                                if lean_obj_tag(v___x_5248_) == 0 {
                                    lean_dec_ref_known(v___x_5248_, 1);
                                    v___x_5249_ = l_Lean_Meta_ArgsPacker_uncurry(
                                        v_argsPacker_5217_,
                                        v_a_5240_,
                                        v___y_5230_,
                                        v___y_5231_,
                                        v___y_5232_,
                                        v___y_5233_,
                                    );
                                    lean_dec(v_a_5240_);
                                    if lean_obj_tag(v___x_5249_) == 0 {
                                        v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
                                        lean_inc(v_a_5250_);
                                        lean_dec_ref_known(v___x_5249_, 1);
                                        v___x_5251_ = lean_box(0);
                                        lean_inc(v_levelParams_5221_);
                                        v___x_5252_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_5221_, v___x_5251_);
                                        lean_inc(v_newFn_5223_);
                                        v___x_5253_ = l_Lean_mkConst(v_newFn_5223_, v___x_5252_);
                                        v___x_5254_ = l_Lean_mkAppN(v___x_5253_, v_ys_5229_);
                                        v_sz_5255_ = lean_array_size(v_preDefs_5214_);
                                        v___x_5256_ = 0usize;
                                        v___x_5257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_5255_, v___x_5256_, v_preDefs_5214_);
                                        v___x_5258_ = l_Lean_Elab_WF_packCalls(
                                            v_fixedParamPerms_5228_,
                                            v_argsPacker_5217_,
                                            v___x_5257_,
                                            v___x_5254_,
                                            v_a_5250_,
                                            v___y_5230_,
                                            v___y_5231_,
                                            v___y_5232_,
                                            v___y_5233_,
                                        );
                                        if lean_obj_tag(v___x_5258_) == 0 {
                                            v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
                                            lean_inc(v_a_5259_);
                                            lean_dec_ref_known(v___x_5258_, 1);
                                            v___x_5260_ = l_Lean_Meta_mkLambdaFVars(
                                                v_ys_5229_,
                                                v_a_5259_,
                                                v___x_5218_,
                                                v___x_5243_,
                                                v___x_5218_,
                                                v___x_5243_,
                                                v___x_5244_,
                                                v___y_5230_,
                                                v___y_5231_,
                                                v___y_5232_,
                                                v___y_5233_,
                                            );
                                            lean_dec_ref(v_ys_5229_);
                                            if lean_obj_tag(v___x_5260_) == 0 {
                                                v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
                                                v_isSharedCheck_5269_ =
                                                    (!lean_is_exclusive(v___x_5260_)) as u8;
                                                if v_isSharedCheck_5269_ == 0 {
                                                    v___x_5263_ = v___x_5260_;
                                                    v_isShared_5264_ = v_isSharedCheck_5269_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5261_);
                                                    lean_dec(v___x_5260_);
                                                    v___x_5263_ = lean_box(0);
                                                    v_isShared_5264_ = v_isSharedCheck_5269_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_a_5246_);
                                                lean_dec_ref(v_termination_5227_);
                                                lean_dec(v_numSectionVars_5225_);
                                                lean_dec(v_binders_5224_);
                                                lean_dec(v_newFn_5223_);
                                                lean_dec_ref(v_modifiers_5222_);
                                                lean_dec(v_levelParams_5221_);
                                                lean_dec(v_ref_5219_);
                                                v_a_5270_ = lean_ctor_get(v___x_5260_, 0);
                                                v_isSharedCheck_5277_ =
                                                    (!lean_is_exclusive(v___x_5260_)) as u8;
                                                if v_isSharedCheck_5277_ == 0 {
                                                    v___x_5272_ = v___x_5260_;
                                                    v_isShared_5273_ = v_isSharedCheck_5277_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5270_);
                                                    lean_dec(v___x_5260_);
                                                    v___x_5272_ = lean_box(0);
                                                    v_isShared_5273_ = v_isSharedCheck_5277_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_5246_);
                                            lean_dec_ref(v_ys_5229_);
                                            lean_dec_ref(v_termination_5227_);
                                            lean_dec(v_numSectionVars_5225_);
                                            lean_dec(v_binders_5224_);
                                            lean_dec(v_newFn_5223_);
                                            lean_dec_ref(v_modifiers_5222_);
                                            lean_dec(v_levelParams_5221_);
                                            lean_dec(v_ref_5219_);
                                            v_a_5278_ = lean_ctor_get(v___x_5258_, 0);
                                            v_isSharedCheck_5285_ =
                                                (!lean_is_exclusive(v___x_5258_)) as u8;
                                            if v_isSharedCheck_5285_ == 0 {
                                                v___x_5280_ = v___x_5258_;
                                                v_isShared_5281_ = v_isSharedCheck_5285_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5278_);
                                                lean_dec(v___x_5258_);
                                                v___x_5280_ = lean_box(0);
                                                v_isShared_5281_ = v_isSharedCheck_5285_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_5246_);
                                        lean_dec_ref(v_ys_5229_);
                                        lean_dec_ref(v_fixedParamPerms_5228_);
                                        lean_dec_ref(v_termination_5227_);
                                        lean_dec(v_numSectionVars_5225_);
                                        lean_dec(v_binders_5224_);
                                        lean_dec(v_newFn_5223_);
                                        lean_dec_ref(v_modifiers_5222_);
                                        lean_dec(v_levelParams_5221_);
                                        lean_dec(v_ref_5219_);
                                        lean_dec_ref(v_argsPacker_5217_);
                                        lean_dec_ref(v_preDefs_5214_);
                                        v_a_5286_ = lean_ctor_get(v___x_5249_, 0);
                                        v_isSharedCheck_5293_ =
                                            (!lean_is_exclusive(v___x_5249_)) as u8;
                                        if v_isSharedCheck_5293_ == 0 {
                                            v___x_5288_ = v___x_5249_;
                                            v_isShared_5289_ = v_isSharedCheck_5293_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5286_);
                                            lean_dec(v___x_5249_);
                                            v___x_5288_ = lean_box(0);
                                            v_isShared_5289_ = v_isSharedCheck_5293_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5246_);
                                    lean_dec(v_a_5240_);
                                    lean_dec_ref(v_ys_5229_);
                                    lean_dec_ref(v_fixedParamPerms_5228_);
                                    lean_dec_ref(v_termination_5227_);
                                    lean_dec(v_numSectionVars_5225_);
                                    lean_dec(v_binders_5224_);
                                    lean_dec(v_newFn_5223_);
                                    lean_dec_ref(v_modifiers_5222_);
                                    lean_dec(v_levelParams_5221_);
                                    lean_dec(v_ref_5219_);
                                    lean_dec_ref(v_argsPacker_5217_);
                                    lean_dec_ref(v_preDefs_5214_);
                                    v_a_5294_ = lean_ctor_get(v___x_5248_, 0);
                                    v_isSharedCheck_5301_ = (!lean_is_exclusive(v___x_5248_)) as u8;
                                    if v_isSharedCheck_5301_ == 0 {
                                        v___x_5296_ = v___x_5248_;
                                        v_isShared_5297_ = v_isSharedCheck_5301_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5294_);
                                        lean_dec(v___x_5248_);
                                        v___x_5296_ = lean_box(0);
                                        v_isShared_5297_ = v_isSharedCheck_5301_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5240_);
                                lean_dec_ref(v_ys_5229_);
                                lean_dec_ref(v_fixedParamPerms_5228_);
                                lean_dec_ref(v_termination_5227_);
                                lean_dec_ref(v_value_5226_);
                                lean_dec(v_numSectionVars_5225_);
                                lean_dec(v_binders_5224_);
                                lean_dec(v_newFn_5223_);
                                lean_dec_ref(v_modifiers_5222_);
                                lean_dec(v_levelParams_5221_);
                                lean_dec(v_ref_5219_);
                                lean_dec_ref(v_argsPacker_5217_);
                                lean_dec_ref(v_preDefs_5214_);
                                v_a_5302_ = lean_ctor_get(v___x_5245_, 0);
                                v_isSharedCheck_5309_ = (!lean_is_exclusive(v___x_5245_)) as u8;
                                if v_isSharedCheck_5309_ == 0 {
                                    v___x_5304_ = v___x_5245_;
                                    v_isShared_5305_ = v_isSharedCheck_5309_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_5302_);
                                    lean_dec(v___x_5245_);
                                    v___x_5304_ = lean_box(0);
                                    v_isShared_5305_ = v_isSharedCheck_5309_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5240_);
                            lean_dec_ref(v_ys_5229_);
                            lean_dec_ref(v_fixedParamPerms_5228_);
                            lean_dec_ref(v_termination_5227_);
                            lean_dec_ref(v_value_5226_);
                            lean_dec(v_numSectionVars_5225_);
                            lean_dec(v_binders_5224_);
                            lean_dec(v_newFn_5223_);
                            lean_dec_ref(v_modifiers_5222_);
                            lean_dec(v_levelParams_5221_);
                            lean_dec(v_ref_5219_);
                            lean_dec_ref(v_argsPacker_5217_);
                            lean_dec_ref(v_preDefs_5214_);
                            v_a_5310_ = lean_ctor_get(v___x_5241_, 0);
                            v_isSharedCheck_5317_ = (!lean_is_exclusive(v___x_5241_)) as u8;
                            if v_isSharedCheck_5317_ == 0 {
                                v___x_5312_ = v___x_5241_;
                                v_isShared_5313_ = v_isSharedCheck_5317_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_5310_);
                                lean_dec(v___x_5241_);
                                v___x_5312_ = lean_box(0);
                                v_isShared_5313_ = v_isSharedCheck_5317_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5238_);
                        lean_dec_ref(v_ys_5229_);
                        lean_dec_ref(v_fixedParamPerms_5228_);
                        lean_dec_ref(v_termination_5227_);
                        lean_dec_ref(v_value_5226_);
                        lean_dec(v_numSectionVars_5225_);
                        lean_dec(v_binders_5224_);
                        lean_dec(v_newFn_5223_);
                        lean_dec_ref(v_modifiers_5222_);
                        lean_dec(v_levelParams_5221_);
                        lean_dec(v_ref_5219_);
                        lean_dec_ref(v_argsPacker_5217_);
                        lean_dec_ref(v_preDefs_5214_);
                        v_a_5318_ = lean_ctor_get(v___x_5239_, 0);
                        v_isSharedCheck_5325_ = (!lean_is_exclusive(v___x_5239_)) as u8;
                        if v_isSharedCheck_5325_ == 0 {
                            v___x_5320_ = v___x_5239_;
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5318_);
                            lean_dec(v___x_5239_);
                            v___x_5320_ = lean_box(0);
                            v_isShared_5321_ = v_isSharedCheck_5325_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_5236_);
                    lean_dec_ref(v_ys_5229_);
                    lean_dec_ref(v_fixedParamPerms_5228_);
                    lean_dec_ref(v_termination_5227_);
                    lean_dec_ref(v_value_5226_);
                    lean_dec(v_numSectionVars_5225_);
                    lean_dec(v_binders_5224_);
                    lean_dec(v_newFn_5223_);
                    lean_dec_ref(v_modifiers_5222_);
                    lean_dec(v_levelParams_5221_);
                    lean_dec(v_ref_5219_);
                    lean_dec_ref(v_argsPacker_5217_);
                    lean_dec(v___x_5216_);
                    lean_dec_ref(v_preDefs_5214_);
                    v_a_5326_ = lean_ctor_get(v___x_5237_, 0);
                    v_isSharedCheck_5333_ = (!lean_is_exclusive(v___x_5237_)) as u8;
                    if v_isSharedCheck_5333_ == 0 {
                        v___x_5328_ = v___x_5237_;
                        v_isShared_5329_ = v_isSharedCheck_5333_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5326_);
                        lean_dec(v___x_5237_);
                        v___x_5328_ = lean_box(0);
                        v_isShared_5329_ = v_isSharedCheck_5333_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5265_ = lean_alloc_ctor(0, 9, (1) as u32);
                lean_ctor_set(v___x_5265_, 0, v_ref_5219_);
                lean_ctor_set(v___x_5265_, 1, v_levelParams_5221_);
                lean_ctor_set(v___x_5265_, 2, v_modifiers_5222_);
                lean_ctor_set(v___x_5265_, 3, v_newFn_5223_);
                lean_ctor_set(v___x_5265_, 4, v_binders_5224_);
                lean_ctor_set(v___x_5265_, 5, v_numSectionVars_5225_);
                lean_ctor_set(v___x_5265_, 6, v_a_5246_);
                lean_ctor_set(v___x_5265_, 7, v_a_5261_);
                lean_ctor_set(v___x_5265_, 8, v_termination_5227_);
                lean_ctor_set_uint8(
                    v___x_5265_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    v_kind_5220_,
                );
                if v_isShared_5264_ == 0 {
                    lean_ctor_set(v___x_5263_, 0, v___x_5265_);
                    v___x_5267_ = v___x_5263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5265_);
                    v___x_5267_ = v_reuseFailAlloc_5268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5267_;
            }
            3 => {
                if v_isShared_5273_ == 0 {
                    v___x_5275_ = v___x_5272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5276_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
                    v___x_5275_ = v_reuseFailAlloc_5276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5275_;
            }
            5 => {
                if v_isShared_5281_ == 0 {
                    v___x_5283_ = v___x_5280_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5284_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_a_5278_);
                    v___x_5283_ = v_reuseFailAlloc_5284_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5283_;
            }
            7 => {
                if v_isShared_5289_ == 0 {
                    v___x_5291_ = v___x_5288_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
                    v___x_5291_ = v_reuseFailAlloc_5292_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5291_;
            }
            9 => {
                if v_isShared_5297_ == 0 {
                    v___x_5299_ = v___x_5296_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
                    v___x_5299_ = v_reuseFailAlloc_5300_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5299_;
            }
            11 => {
                if v_isShared_5305_ == 0 {
                    v___x_5307_ = v___x_5304_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
                    v___x_5307_ = v_reuseFailAlloc_5308_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5307_;
            }
            13 => {
                if v_isShared_5313_ == 0 {
                    v___x_5315_ = v___x_5312_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5315_;
            }
            15 => {
                if v_isShared_5321_ == 0 {
                    v___x_5323_ = v___x_5320_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
                    v___x_5323_ = v_reuseFailAlloc_5324_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5323_;
            }
            17 => {
                if v_isShared_5329_ == 0 {
                    v___x_5331_ = v___x_5328_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
                    v___x_5331_ = v_reuseFailAlloc_5332_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_packMutual___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_preDefs_5334_: *mut LeanObject = *_args.add(0);
    let mut v_perms_5335_: *mut LeanObject = *_args.add(1);
    let mut v___x_5336_: *mut LeanObject = *_args.add(2);
    let mut v_argsPacker_5337_: *mut LeanObject = *_args.add(3);
    let mut v___x_5338_: *mut LeanObject = *_args.add(4);
    let mut v_ref_5339_: *mut LeanObject = *_args.add(5);
    let mut v_kind_5340_: *mut LeanObject = *_args.add(6);
    let mut v_levelParams_5341_: *mut LeanObject = *_args.add(7);
    let mut v_modifiers_5342_: *mut LeanObject = *_args.add(8);
    let mut v_newFn_5343_: *mut LeanObject = *_args.add(9);
    let mut v_binders_5344_: *mut LeanObject = *_args.add(10);
    let mut v_numSectionVars_5345_: *mut LeanObject = *_args.add(11);
    let mut v_value_5346_: *mut LeanObject = *_args.add(12);
    let mut v_termination_5347_: *mut LeanObject = *_args.add(13);
    let mut v_fixedParamPerms_5348_: *mut LeanObject = *_args.add(14);
    let mut v_ys_5349_: *mut LeanObject = *_args.add(15);
    let mut v___y_5350_: *mut LeanObject = *_args.add(16);
    let mut v___y_5351_: *mut LeanObject = *_args.add(17);
    let mut v___y_5352_: *mut LeanObject = *_args.add(18);
    let mut v___y_5353_: *mut LeanObject = *_args.add(19);
    let mut v___y_5354_: *mut LeanObject = *_args.add(20);
    let mut v___x_2523__boxed_5355_: u8 = 0;
    let mut v_kind_boxed_5356_: u8 = 0;
    let mut v_res_5357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2523__boxed_5355_ = (lean_unbox(v___x_5338_) as u8);
    v_kind_boxed_5356_ = (lean_unbox(v_kind_5340_) as u8);
    v_res_5357_ = l_Lean_Elab_WF_packMutual___lam__0(
        v_preDefs_5334_,
        v_perms_5335_,
        v___x_5336_,
        v_argsPacker_5337_,
        v___x_2523__boxed_5355_,
        v_ref_5339_,
        v_kind_boxed_5356_,
        v_levelParams_5341_,
        v_modifiers_5342_,
        v_newFn_5343_,
        v_binders_5344_,
        v_numSectionVars_5345_,
        v_value_5346_,
        v_termination_5347_,
        v_fixedParamPerms_5348_,
        v_ys_5349_,
        v___y_5350_,
        v___y_5351_,
        v___y_5352_,
        v___y_5353_,
    );
    lean_dec(v___y_5353_);
    lean_dec_ref(v___y_5352_);
    lean_dec(v___y_5351_);
    lean_dec_ref(v___y_5350_);
    lean_dec_ref(v_perms_5335_);
    return v_res_5357_;
}
pub unsafe fn l_Lean_Elab_WF_packMutual(
    mut v_fixedParamPerms_5358_: *mut LeanObject,
    mut v_argsPacker_5359_: *mut LeanObject,
    mut v_preDefs_5360_: *mut LeanObject,
    mut v_a_5361_: *mut LeanObject,
    mut v_a_5362_: *mut LeanObject,
    mut v_a_5363_: *mut LeanObject,
    mut v_a_5364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5370_: u8 = 0;
    let mut v_levelParams_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termination_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newFn_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    v___x_5366_ = l_Lean_Elab_instInhabitedPreDefinition_default;
    v___x_5367_ = lean_unsigned_to_nat(0);
    v___x_5368_ = lean_array_get_borrowed(v___x_5366_, v_preDefs_5360_, v___x_5367_);
    v_ref_5369_ = lean_ctor_get(v___x_5368_, 0);
    v_kind_5370_ = lean_ctor_get_uint8(
        v___x_5368_,
        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
    );
    v_levelParams_5371_ = lean_ctor_get(v___x_5368_, 1);
    v_modifiers_5372_ = lean_ctor_get(v___x_5368_, 2);
    v_declName_5373_ = lean_ctor_get(v___x_5368_, 3);
    v_binders_5374_ = lean_ctor_get(v___x_5368_, 4);
    v_numSectionVars_5375_ = lean_ctor_get(v___x_5368_, 5);
    v_type_5376_ = lean_ctor_get(v___x_5368_, 6);
    v_value_5377_ = lean_ctor_get(v___x_5368_, 7);
    v_termination_5378_ = lean_ctor_get(v___x_5368_, 8);
    lean_inc_ref(v_fixedParamPerms_5358_);
    v_newFn_5379_ =
        l_Lean_Elab_WF_mutualName(v_fixedParamPerms_5358_, v_argsPacker_5359_, v_preDefs_5360_);
    v___x_5380_ = lean_name_eq(v_newFn_5379_, v_declName_5373_);
    if v___x_5380_ == 0 {
        let mut v_perms_5381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_termination_5378_);
        lean_inc_ref(v_value_5377_);
        lean_inc_ref(v_type_5376_);
        lean_inc(v_numSectionVars_5375_);
        lean_inc(v_binders_5374_);
        lean_inc_ref(v_modifiers_5372_);
        lean_inc(v_levelParams_5371_);
        lean_inc(v_ref_5369_);
        v_perms_5381_ = lean_ctor_get(v_fixedParamPerms_5358_, 1);
        lean_inc_ref_n(v_perms_5381_, 2);
        v___x_5382_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4_once),
            _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4,
        );
        v___x_5383_ = lean_box((v___x_5380_) as usize);
        v___x_5384_ = lean_box((v_kind_5370_) as usize);
        v___f_5385_ = lean_alloc_closure(
            l_Lean_Elab_WF_packMutual___lam__0___boxed as *mut core::ffi::c_void,
            21,
            15,
        );
        lean_closure_set(v___f_5385_, 0, v_preDefs_5360_);
        lean_closure_set(v___f_5385_, 1, v_perms_5381_);
        lean_closure_set(v___f_5385_, 2, v___x_5367_);
        lean_closure_set(v___f_5385_, 3, v_argsPacker_5359_);
        lean_closure_set(v___f_5385_, 4, v___x_5383_);
        lean_closure_set(v___f_5385_, 5, v_ref_5369_);
        lean_closure_set(v___f_5385_, 6, v___x_5384_);
        lean_closure_set(v___f_5385_, 7, v_levelParams_5371_);
        lean_closure_set(v___f_5385_, 8, v_modifiers_5372_);
        lean_closure_set(v___f_5385_, 9, v_newFn_5379_);
        lean_closure_set(v___f_5385_, 10, v_binders_5374_);
        lean_closure_set(v___f_5385_, 11, v_numSectionVars_5375_);
        lean_closure_set(v___f_5385_, 12, v_value_5377_);
        lean_closure_set(v___f_5385_, 13, v_termination_5378_);
        lean_closure_set(v___f_5385_, 14, v_fixedParamPerms_5358_);
        v___x_5386_ = lean_array_get(v___x_5382_, v_perms_5381_, v___x_5367_);
        lean_dec_ref(v_perms_5381_);
        v___x_5387_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_5386_, v_type_5376_, v___f_5385_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_);
        return v___x_5387_;
    } else {
        let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___x_5368_);
        lean_dec(v_newFn_5379_);
        lean_dec_ref(v_preDefs_5360_);
        lean_dec_ref(v_argsPacker_5359_);
        lean_dec_ref(v_fixedParamPerms_5358_);
        v___x_5388_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5388_, 0, v___x_5368_);
        return v___x_5388_;
    }
}
pub unsafe fn l_Lean_Elab_WF_packMutual___boxed(
    mut v_fixedParamPerms_5389_: *mut LeanObject,
    mut v_argsPacker_5390_: *mut LeanObject,
    mut v_preDefs_5391_: *mut LeanObject,
    mut v_a_5392_: *mut LeanObject,
    mut v_a_5393_: *mut LeanObject,
    mut v_a_5394_: *mut LeanObject,
    mut v_a_5395_: *mut LeanObject,
    mut v_a_5396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5397_: *mut LeanObject = core::ptr::null_mut();
    v_res_5397_ = l_Lean_Elab_WF_packMutual(
        v_fixedParamPerms_5389_,
        v_argsPacker_5390_,
        v_preDefs_5391_,
        v_a_5392_,
        v_a_5393_,
        v_a_5394_,
        v_a_5395_,
    );
    lean_dec(v_a_5395_);
    lean_dec_ref(v_a_5394_);
    lean_dec(v_a_5393_);
    lean_dec_ref(v_a_5392_);
    return v_res_5397_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0(
    mut v___x_5398_: *mut LeanObject,
    mut v_ys_5399_: *mut LeanObject,
    mut v_as_5400_: *mut LeanObject,
    mut v_i_5401_: *mut LeanObject,
    mut v_j_5402_: *mut LeanObject,
    mut v_inv_5403_: *mut LeanObject,
    mut v_bs_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    v___x_5410_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(
        v___x_5398_,
        v_ys_5399_,
        v_as_5400_,
        v_i_5401_,
        v_j_5402_,
        v_bs_5404_,
        v___y_5405_,
        v___y_5406_,
        v___y_5407_,
        v___y_5408_,
    );
    return v___x_5410_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(
    mut v___x_5411_: *mut LeanObject,
    mut v_ys_5412_: *mut LeanObject,
    mut v_as_5413_: *mut LeanObject,
    mut v_i_5414_: *mut LeanObject,
    mut v_j_5415_: *mut LeanObject,
    mut v_inv_5416_: *mut LeanObject,
    mut v_bs_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5423_: *mut LeanObject = core::ptr::null_mut();
    v_res_5423_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0(
        v___x_5411_,
        v_ys_5412_,
        v_as_5413_,
        v_i_5414_,
        v_j_5415_,
        v_inv_5416_,
        v_bs_5417_,
        v___y_5418_,
        v___y_5419_,
        v___y_5420_,
        v___y_5421_,
    );
    lean_dec(v___y_5421_);
    lean_dec_ref(v___y_5420_);
    lean_dec(v___y_5419_);
    lean_dec_ref(v___y_5418_);
    lean_dec_ref(v_as_5413_);
    lean_dec_ref(v___x_5411_);
    return v_res_5423_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1(
    mut v___x_5424_: *mut LeanObject,
    mut v_ys_5425_: *mut LeanObject,
    mut v_as_5426_: *mut LeanObject,
    mut v_i_5427_: *mut LeanObject,
    mut v_j_5428_: *mut LeanObject,
    mut v_inv_5429_: *mut LeanObject,
    mut v_bs_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    v___x_5436_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(
        v___x_5424_,
        v_ys_5425_,
        v_as_5426_,
        v_i_5427_,
        v_j_5428_,
        v_bs_5430_,
        v___y_5431_,
        v___y_5432_,
        v___y_5433_,
        v___y_5434_,
    );
    return v___x_5436_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(
    mut v___x_5437_: *mut LeanObject,
    mut v_ys_5438_: *mut LeanObject,
    mut v_as_5439_: *mut LeanObject,
    mut v_i_5440_: *mut LeanObject,
    mut v_j_5441_: *mut LeanObject,
    mut v_inv_5442_: *mut LeanObject,
    mut v_bs_5443_: *mut LeanObject,
    mut v___y_5444_: *mut LeanObject,
    mut v___y_5445_: *mut LeanObject,
    mut v___y_5446_: *mut LeanObject,
    mut v___y_5447_: *mut LeanObject,
    mut v___y_5448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5449_: *mut LeanObject = core::ptr::null_mut();
    v_res_5449_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1(
        v___x_5437_,
        v_ys_5438_,
        v_as_5439_,
        v_i_5440_,
        v_j_5441_,
        v_inv_5442_,
        v_bs_5443_,
        v___y_5444_,
        v___y_5445_,
        v___y_5446_,
        v___y_5447_,
    );
    lean_dec(v___y_5447_);
    lean_dec_ref(v___y_5446_);
    lean_dec(v___y_5445_);
    lean_dec_ref(v___y_5444_);
    lean_dec_ref(v_as_5439_);
    lean_dec_ref(v___x_5437_);
    return v_res_5449_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(
    mut v_e_5450_: *mut LeanObject,
    mut v_k_5451_: *mut LeanObject,
    mut v_cleanupAnnotations_5452_: u8,
    mut v___y_5453_: *mut LeanObject,
    mut v___y_5454_: *mut LeanObject,
    mut v___y_5455_: *mut LeanObject,
    mut v___y_5456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: u8 = 0;
    let mut v___x_5460_: u8 = 0;
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5470_: u8 = 0;
    let mut v_a_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5474_: u8 = 0;
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5458_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_5458_, 0, v_k_5451_);
                v___x_5459_ = 1;
                v___x_5460_ = 0;
                v___x_5461_ = lean_box(0);
                v___x_5462_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
                    v_e_5450_,
                    v___x_5459_,
                    v___x_5460_,
                    v___x_5459_,
                    v___x_5460_,
                    v___x_5461_,
                    v___f_5458_,
                    v_cleanupAnnotations_5452_,
                    v___y_5453_,
                    v___y_5454_,
                    v___y_5455_,
                    v___y_5456_,
                );
                if lean_obj_tag(v___x_5462_) == 0 {
                    v_a_5463_ = lean_ctor_get(v___x_5462_, 0);
                    v_isSharedCheck_5470_ = (!lean_is_exclusive(v___x_5462_)) as u8;
                    if v_isSharedCheck_5470_ == 0 {
                        v___x_5465_ = v___x_5462_;
                        v_isShared_5466_ = v_isSharedCheck_5470_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5463_);
                        lean_dec(v___x_5462_);
                        v___x_5465_ = lean_box(0);
                        v_isShared_5466_ = v_isSharedCheck_5470_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5471_ = lean_ctor_get(v___x_5462_, 0);
                    v_isSharedCheck_5478_ = (!lean_is_exclusive(v___x_5462_)) as u8;
                    if v_isSharedCheck_5478_ == 0 {
                        v___x_5473_ = v___x_5462_;
                        v_isShared_5474_ = v_isSharedCheck_5478_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5471_);
                        lean_dec(v___x_5462_);
                        v___x_5473_ = lean_box(0);
                        v_isShared_5474_ = v_isSharedCheck_5478_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5466_ == 0 {
                    v___x_5468_ = v___x_5465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
                    v___x_5468_ = v_reuseFailAlloc_5469_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5468_;
            }
            3 => {
                if v_isShared_5474_ == 0 {
                    v___x_5476_ = v___x_5473_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5477_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5471_);
                    v___x_5476_ = v_reuseFailAlloc_5477_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(
    mut v_e_5479_: *mut LeanObject,
    mut v_k_5480_: *mut LeanObject,
    mut v_cleanupAnnotations_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5487_: u8 = 0;
    let mut v_res_5488_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5487_ = (lean_unbox(v_cleanupAnnotations_5481_) as u8);
    v_res_5488_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(
            v_e_5479_,
            v_k_5480_,
            v_cleanupAnnotations_boxed_5487_,
            v___y_5482_,
            v___y_5483_,
            v___y_5484_,
            v___y_5485_,
        );
    lean_dec(v___y_5485_);
    lean_dec_ref(v___y_5484_);
    lean_dec(v___y_5483_);
    lean_dec_ref(v___y_5482_);
    return v_res_5488_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(
    mut v_00_u03b1_5489_: *mut LeanObject,
    mut v_e_5490_: *mut LeanObject,
    mut v_k_5491_: *mut LeanObject,
    mut v_cleanupAnnotations_5492_: u8,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    v___x_5498_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(
            v_e_5490_,
            v_k_5491_,
            v_cleanupAnnotations_5492_,
            v___y_5493_,
            v___y_5494_,
            v___y_5495_,
            v___y_5496_,
        );
    return v___x_5498_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(
    mut v_00_u03b1_5499_: *mut LeanObject,
    mut v_e_5500_: *mut LeanObject,
    mut v_k_5501_: *mut LeanObject,
    mut v_cleanupAnnotations_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5508_: u8 = 0;
    let mut v_res_5509_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5508_ = (lean_unbox(v_cleanupAnnotations_5502_) as u8);
    v_res_5509_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(
        v_00_u03b1_5499_,
        v_e_5500_,
        v_k_5501_,
        v_cleanupAnnotations_boxed_5508_,
        v___y_5503_,
        v___y_5504_,
        v___y_5505_,
        v___y_5506_,
    );
    lean_dec(v___y_5506_);
    lean_dec_ref(v___y_5505_);
    lean_dec(v___y_5504_);
    lean_dec_ref(v___y_5503_);
    return v_res_5509_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(
    mut v_msg_5510_: *mut LeanObject,
    mut v___y_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717__overap_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    v___f_5516_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0;
    v___x_1717__overap_5517_ = lean_panic_fn_borrowed(v___f_5516_, v_msg_5510_);
    lean_inc(v___y_5514_);
    lean_inc_ref(v___y_5513_);
    lean_inc(v___y_5512_);
    lean_inc_ref(v___y_5511_);
    v___x_5518_ = lean_apply_5(
        v___x_1717__overap_5517_,
        v___y_5511_,
        v___y_5512_,
        v___y_5513_,
        v___y_5514_,
        lean_box(0),
    );
    return v___x_5518_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(
    mut v_msg_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
    mut v___y_5522_: *mut LeanObject,
    mut v___y_5523_: *mut LeanObject,
    mut v___y_5524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5525_: *mut LeanObject = core::ptr::null_mut();
    v_res_5525_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(
        v_msg_5519_,
        v___y_5520_,
        v___y_5521_,
        v___y_5522_,
        v___y_5523_,
    );
    lean_dec(v___y_5523_);
    lean_dec_ref(v___y_5522_);
    lean_dec(v___y_5521_);
    lean_dec_ref(v___y_5520_);
    return v_res_5525_;
}
pub unsafe fn l_Lean_Elab_WF_varyingVarNames___lam__0(
    mut v_xs_5526_: *mut LeanObject,
    mut v_x_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    v___x_5533_ = lean_array_get_size(v_xs_5526_);
    v___x_5534_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5534_, 0, v___x_5533_);
    return v___x_5534_;
}
pub unsafe fn l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(
    mut v_xs_5535_: *mut LeanObject,
    mut v_x_5536_: *mut LeanObject,
    mut v___y_5537_: *mut LeanObject,
    mut v___y_5538_: *mut LeanObject,
    mut v___y_5539_: *mut LeanObject,
    mut v___y_5540_: *mut LeanObject,
    mut v___y_5541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5542_: *mut LeanObject = core::ptr::null_mut();
    v_res_5542_ = l_Lean_Elab_WF_varyingVarNames___lam__0(
        v_xs_5535_,
        v_x_5536_,
        v___y_5537_,
        v___y_5538_,
        v___y_5539_,
        v___y_5540_,
    );
    lean_dec(v___y_5540_);
    lean_dec_ref(v___y_5539_);
    lean_dec(v___y_5538_);
    lean_dec_ref(v___y_5537_);
    lean_dec_ref(v_x_5536_);
    lean_dec_ref(v_xs_5535_);
    return v_res_5542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(
    mut v_as_5543_: *mut LeanObject,
    mut v_sz_5544_: usize,
    mut v_i_5545_: usize,
    mut v_b_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: usize = 0;
    let mut v___x_5554_: usize = 0;
    let mut v___x_5556_: u8 = 0;
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v_array_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: u8 = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5573_: u8 = 0;
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5590_: u8 = 0;
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut v_unused_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5556_ = lean_usize_dec_lt(v_i_5545_, v_sz_5544_);
                if v___x_5556_ == 0 {
                    v___x_5557_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5557_, 0, v_b_5546_);
                    return v___x_5557_;
                } else {
                    v_snd_5558_ = lean_ctor_get(v_b_5546_, 1);
                    v_fst_5559_ = lean_ctor_get(v_b_5546_, 0);
                    v_isSharedCheck_5603_ = (!lean_is_exclusive(v_b_5546_)) as u8;
                    if v_isSharedCheck_5603_ == 0 {
                        v___x_5561_ = v_b_5546_;
                        v_isShared_5562_ = v_isSharedCheck_5603_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_5558_);
                        lean_inc(v_fst_5559_);
                        lean_dec(v_b_5546_);
                        v___x_5561_ = lean_box(0);
                        v_isShared_5562_ = v_isSharedCheck_5603_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5553_ = 1usize;
                v___x_5554_ = lean_usize_add(v_i_5545_, v___x_5553_);
                v_i_5545_ = v___x_5554_;
                v_b_5546_ = v_a_5552_;
                state = 0;
                continue;
            }
            2 => {
                v_array_5563_ = lean_ctor_get(v_snd_5558_, 0);
                v_start_5564_ = lean_ctor_get(v_snd_5558_, 1);
                v_stop_5565_ = lean_ctor_get(v_snd_5558_, 2);
                v___x_5566_ = lean_nat_dec_lt(v_start_5564_, v_stop_5565_);
                if v___x_5566_ == 0 {
                    if v_isShared_5562_ == 0 {
                        v___x_5568_ = v___x_5561_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_fst_5559_);
                        lean_ctor_set(v_reuseFailAlloc_5570_, 1, v_snd_5558_);
                        v___x_5568_ = v_reuseFailAlloc_5570_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_5565_);
                    lean_inc(v_start_5564_);
                    lean_inc_ref(v_array_5563_);
                    v_isSharedCheck_5599_ = (!lean_is_exclusive(v_snd_5558_)) as u8;
                    if v_isSharedCheck_5599_ == 0 {
                        v_unused_5600_ = lean_ctor_get(v_snd_5558_, 2);
                        lean_dec(v_unused_5600_);
                        v_unused_5601_ = lean_ctor_get(v_snd_5558_, 1);
                        lean_dec(v_unused_5601_);
                        v_unused_5602_ = lean_ctor_get(v_snd_5558_, 0);
                        lean_dec(v_unused_5602_);
                        v___x_5572_ = v_snd_5558_;
                        v_isShared_5573_ = v_isSharedCheck_5599_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_snd_5558_);
                        v___x_5572_ = lean_box(0);
                        v_isShared_5573_ = v_isSharedCheck_5599_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5569_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5569_, 0, v___x_5568_);
                return v___x_5569_;
            }
            4 => {
                v___x_5574_ = lean_array_fget(v_array_5563_, v_start_5564_);
                v___x_5575_ = lean_unsigned_to_nat(1);
                v___x_5576_ = lean_nat_add(v_start_5564_, v___x_5575_);
                lean_dec(v_start_5564_);
                if v_isShared_5573_ == 0 {
                    lean_ctor_set(v___x_5572_, 1, v___x_5576_);
                    v___x_5578_ = v___x_5572_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5598_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_array_5563_);
                    lean_ctor_set(v_reuseFailAlloc_5598_, 1, v___x_5576_);
                    lean_ctor_set(v_reuseFailAlloc_5598_, 2, v_stop_5565_);
                    v___x_5578_ = v_reuseFailAlloc_5598_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if lean_obj_tag(v___x_5574_) == 0 {
                    v_a_5579_ = lean_array_uget_borrowed(v_as_5543_, v_i_5545_);
                    v___x_5580_ = l_Lean_Expr_fvarId_x21(v_a_5579_);
                    v___x_5581_ = l_Lean_FVarId_getUserName___redArg(
                        v___x_5580_,
                        v___y_5547_,
                        v___y_5548_,
                        v___y_5549_,
                    );
                    if lean_obj_tag(v___x_5581_) == 0 {
                        v_a_5582_ = lean_ctor_get(v___x_5581_, 0);
                        lean_inc(v_a_5582_);
                        lean_dec_ref_known(v___x_5581_, 1);
                        v___x_5583_ = lean_array_push(v_fst_5559_, v_a_5582_);
                        if v_isShared_5562_ == 0 {
                            lean_ctor_set(v___x_5561_, 1, v___x_5578_);
                            lean_ctor_set(v___x_5561_, 0, v___x_5583_);
                            v___x_5585_ = v___x_5561_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
                            lean_ctor_set(v_reuseFailAlloc_5586_, 1, v___x_5578_);
                            v___x_5585_ = v_reuseFailAlloc_5586_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_5578_);
                        lean_del_object(v___x_5561_);
                        lean_dec(v_fst_5559_);
                        v_a_5587_ = lean_ctor_get(v___x_5581_, 0);
                        v_isSharedCheck_5594_ = (!lean_is_exclusive(v___x_5581_)) as u8;
                        if v_isSharedCheck_5594_ == 0 {
                            v___x_5589_ = v___x_5581_;
                            v_isShared_5590_ = v_isSharedCheck_5594_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5587_);
                            lean_dec(v___x_5581_);
                            v___x_5589_ = lean_box(0);
                            v_isShared_5590_ = v_isSharedCheck_5594_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_5574_, 1);
                    if v_isShared_5562_ == 0 {
                        lean_ctor_set(v___x_5561_, 1, v___x_5578_);
                        v___x_5596_ = v___x_5561_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_fst_5559_);
                        lean_ctor_set(v_reuseFailAlloc_5597_, 1, v___x_5578_);
                        v___x_5596_ = v_reuseFailAlloc_5597_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v_a_5552_ = v___x_5585_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_5590_ == 0 {
                    v___x_5592_ = v___x_5589_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
                    v___x_5592_ = v_reuseFailAlloc_5593_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5592_;
            }
            9 => {
                v_a_5552_ = v___x_5596_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(
    mut v_as_5604_: *mut LeanObject,
    mut v_sz_5605_: *mut LeanObject,
    mut v_i_5606_: *mut LeanObject,
    mut v_b_5607_: *mut LeanObject,
    mut v___y_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5612_: usize = 0;
    let mut v_i_boxed_5613_: usize = 0;
    let mut v_res_5614_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5612_ = lean_unbox_usize(v_sz_5605_);
    lean_dec(v_sz_5605_);
    v_i_boxed_5613_ = lean_unbox_usize(v_i_5606_);
    lean_dec(v_i_5606_);
    v_res_5614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_5604_, v_sz_boxed_5612_, v_i_boxed_5613_, v_b_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
    lean_dec(v___y_5610_);
    lean_dec_ref(v___y_5609_);
    lean_dec_ref(v___y_5608_);
    lean_dec_ref(v_as_5604_);
    return v_res_5614_;
}
pub unsafe fn _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2() -> *mut LeanObject {
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    v___x_5617_ = l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1;
    v___x_5618_ = lean_unsigned_to_nat(4);
    v___x_5619_ = lean_unsigned_to_nat(119);
    v___x_5620_ = l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0;
    v___x_5621_ = l_Lean_Elab_WF_packCalls___lam__2___closed__0;
    v___x_5622_ = l_mkPanicMessageWithDecl(
        v___x_5621_,
        v___x_5620_,
        v___x_5619_,
        v___x_5618_,
        v___x_5617_,
    );
    return v___x_5622_;
}
pub unsafe fn _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    v___x_5624_ = l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3;
    v___x_5625_ = lean_unsigned_to_nat(4);
    v___x_5626_ = lean_unsigned_to_nat(120);
    v___x_5627_ = l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0;
    v___x_5628_ = l_Lean_Elab_WF_packCalls___lam__2___closed__0;
    v___x_5629_ = l_mkPanicMessageWithDecl(
        v___x_5628_,
        v___x_5627_,
        v___x_5626_,
        v___x_5625_,
        v___x_5624_,
    );
    return v___x_5629_;
}
pub unsafe fn l_Lean_Elab_WF_varyingVarNames___lam__1(
    mut v_a_5632_: *mut LeanObject,
    mut v_fixedParamPerms_5633_: *mut LeanObject,
    mut v_preDefIdx_5634_: *mut LeanObject,
    mut v_xs_5635_: *mut LeanObject,
    mut v_x_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: u8 = 0;
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: u8 = 0;
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5657_: usize = 0;
    let mut v___x_5658_: usize = 0;
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5663_: u8 = 0;
    let mut v_fst_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5668_: u8 = 0;
    let mut v_a_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5642_ = lean_array_get_size(v_xs_5635_);
                v___x_5643_ = lean_nat_dec_eq(v___x_5642_, v_a_5632_);
                if v___x_5643_ == 0 {
                    v___x_5644_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once
                        ),
                        _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2,
                    );
                    v___x_5645_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(
                        v___x_5644_,
                        v___y_5637_,
                        v___y_5638_,
                        v___y_5639_,
                        v___y_5640_,
                    );
                    return v___x_5645_;
                } else {
                    v_perms_5646_ = lean_ctor_get(v_fixedParamPerms_5633_, 1);
                    v___x_5647_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4_once),
                        _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4,
                    );
                    v___x_5648_ =
                        lean_array_get_borrowed(v___x_5647_, v_perms_5646_, v_preDefIdx_5634_);
                    v___x_5649_ = lean_array_get_size(v___x_5648_);
                    v___x_5650_ = lean_nat_dec_eq(v___x_5649_, v_a_5632_);
                    if v___x_5650_ == 0 {
                        v___x_5651_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once
                            ),
                            _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4,
                        );
                        v___x_5652_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(
                            v___x_5651_,
                            v___y_5637_,
                            v___y_5638_,
                            v___y_5639_,
                            v___y_5640_,
                        );
                        return v___x_5652_;
                    } else {
                        v___x_5653_ = lean_unsigned_to_nat(0);
                        v___x_5654_ = l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5;
                        lean_inc(v___x_5648_);
                        v___x_5655_ =
                            l_Array_toSubarray___redArg(v___x_5648_, v___x_5653_, v___x_5649_);
                        v___x_5656_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5656_, 0, v___x_5654_);
                        lean_ctor_set(v___x_5656_, 1, v___x_5655_);
                        v_sz_5657_ = lean_array_size(v_xs_5635_);
                        v___x_5658_ = 0usize;
                        v___x_5659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_5635_, v_sz_5657_, v___x_5658_, v___x_5656_, v___y_5637_, v___y_5639_, v___y_5640_);
                        if lean_obj_tag(v___x_5659_) == 0 {
                            v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
                            v_isSharedCheck_5668_ = (!lean_is_exclusive(v___x_5659_)) as u8;
                            if v_isSharedCheck_5668_ == 0 {
                                v___x_5662_ = v___x_5659_;
                                v_isShared_5663_ = v_isSharedCheck_5668_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5660_);
                                lean_dec(v___x_5659_);
                                v___x_5662_ = lean_box(0);
                                v_isShared_5663_ = v_isSharedCheck_5668_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5669_ = lean_ctor_get(v___x_5659_, 0);
                            v_isSharedCheck_5676_ = (!lean_is_exclusive(v___x_5659_)) as u8;
                            if v_isSharedCheck_5676_ == 0 {
                                v___x_5671_ = v___x_5659_;
                                v_isShared_5672_ = v_isSharedCheck_5676_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5669_);
                                lean_dec(v___x_5659_);
                                v___x_5671_ = lean_box(0);
                                v_isShared_5672_ = v_isSharedCheck_5676_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_fst_5664_ = lean_ctor_get(v_a_5660_, 0);
                lean_inc(v_fst_5664_);
                lean_dec(v_a_5660_);
                if v_isShared_5663_ == 0 {
                    lean_ctor_set(v___x_5662_, 0, v_fst_5664_);
                    v___x_5666_ = v___x_5662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_fst_5664_);
                    v___x_5666_ = v_reuseFailAlloc_5667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5666_;
            }
            3 => {
                if v_isShared_5672_ == 0 {
                    v___x_5674_ = v___x_5671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
                    v___x_5674_ = v_reuseFailAlloc_5675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(
    mut v_a_5677_: *mut LeanObject,
    mut v_fixedParamPerms_5678_: *mut LeanObject,
    mut v_preDefIdx_5679_: *mut LeanObject,
    mut v_xs_5680_: *mut LeanObject,
    mut v_x_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5687_: *mut LeanObject = core::ptr::null_mut();
    v_res_5687_ = l_Lean_Elab_WF_varyingVarNames___lam__1(
        v_a_5677_,
        v_fixedParamPerms_5678_,
        v_preDefIdx_5679_,
        v_xs_5680_,
        v_x_5681_,
        v___y_5682_,
        v___y_5683_,
        v___y_5684_,
        v___y_5685_,
    );
    lean_dec(v___y_5685_);
    lean_dec_ref(v___y_5684_);
    lean_dec(v___y_5683_);
    lean_dec_ref(v___y_5682_);
    lean_dec_ref(v_x_5681_);
    lean_dec_ref(v_xs_5680_);
    lean_dec(v_preDefIdx_5679_);
    lean_dec_ref(v_fixedParamPerms_5678_);
    lean_dec(v_a_5677_);
    return v_res_5687_;
}
pub unsafe fn l_Lean_Elab_WF_varyingVarNames(
    mut v_fixedParamPerms_5689_: *mut LeanObject,
    mut v_preDefIdx_5690_: *mut LeanObject,
    mut v_preDef_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
    mut v_a_5693_: *mut LeanObject,
    mut v_a_5694_: *mut LeanObject,
    mut v_a_5695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: u8 = 0;
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5709_: u8 = 0;
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_5697_ = lean_ctor_get(v_preDef_5691_, 6);
                lean_inc_ref(v_type_5697_);
                v_value_5698_ = lean_ctor_get(v_preDef_5691_, 7);
                lean_inc_ref(v_value_5698_);
                lean_dec_ref(v_preDef_5691_);
                v___f_5699_ = l_Lean_Elab_WF_varyingVarNames___closed__0;
                v___x_5700_ = 0;
                v___x_5701_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_5698_, v___f_5699_, v___x_5700_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
                if lean_obj_tag(v___x_5701_) == 0 {
                    v_a_5702_ = lean_ctor_get(v___x_5701_, 0);
                    lean_inc_n(v_a_5702_, 2);
                    lean_dec_ref_known(v___x_5701_, 1);
                    v___f_5703_ = lean_alloc_closure(
                        l_Lean_Elab_WF_varyingVarNames___lam__1___boxed as *mut core::ffi::c_void,
                        10,
                        3,
                    );
                    lean_closure_set(v___f_5703_, 0, v_a_5702_);
                    lean_closure_set(v___f_5703_, 1, v_fixedParamPerms_5689_);
                    lean_closure_set(v___f_5703_, 2, v_preDefIdx_5690_);
                    v___x_5704_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5704_, 0, v_a_5702_);
                    v___x_5705_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_5697_, v___x_5704_, v___f_5703_, v___x_5700_, v___x_5700_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
                    return v___x_5705_;
                } else {
                    lean_dec_ref(v_type_5697_);
                    lean_dec(v_preDefIdx_5690_);
                    lean_dec_ref(v_fixedParamPerms_5689_);
                    v_a_5706_ = lean_ctor_get(v___x_5701_, 0);
                    v_isSharedCheck_5713_ = (!lean_is_exclusive(v___x_5701_)) as u8;
                    if v_isSharedCheck_5713_ == 0 {
                        v___x_5708_ = v___x_5701_;
                        v_isShared_5709_ = v_isSharedCheck_5713_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5706_);
                        lean_dec(v___x_5701_);
                        v___x_5708_ = lean_box(0);
                        v_isShared_5709_ = v_isSharedCheck_5713_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5709_ == 0 {
                    v___x_5711_ = v___x_5708_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5712_, 0, v_a_5706_);
                    v___x_5711_ = v_reuseFailAlloc_5712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_varyingVarNames___boxed(
    mut v_fixedParamPerms_5714_: *mut LeanObject,
    mut v_preDefIdx_5715_: *mut LeanObject,
    mut v_preDef_5716_: *mut LeanObject,
    mut v_a_5717_: *mut LeanObject,
    mut v_a_5718_: *mut LeanObject,
    mut v_a_5719_: *mut LeanObject,
    mut v_a_5720_: *mut LeanObject,
    mut v_a_5721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5722_: *mut LeanObject = core::ptr::null_mut();
    v_res_5722_ = l_Lean_Elab_WF_varyingVarNames(
        v_fixedParamPerms_5714_,
        v_preDefIdx_5715_,
        v_preDef_5716_,
        v_a_5717_,
        v_a_5718_,
        v_a_5719_,
        v_a_5720_,
    );
    lean_dec(v_a_5720_);
    lean_dec_ref(v_a_5719_);
    lean_dec(v_a_5718_);
    lean_dec_ref(v_a_5717_);
    return v_res_5722_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(
    mut v_as_5723_: *mut LeanObject,
    mut v_sz_5724_: usize,
    mut v_i_5725_: usize,
    mut v_b_5726_: *mut LeanObject,
    mut v___y_5727_: *mut LeanObject,
    mut v___y_5728_: *mut LeanObject,
    mut v___y_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    v___x_5732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_5723_, v_sz_5724_, v_i_5725_, v_b_5726_, v___y_5727_, v___y_5729_, v___y_5730_);
    return v___x_5732_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(
    mut v_as_5733_: *mut LeanObject,
    mut v_sz_5734_: *mut LeanObject,
    mut v_i_5735_: *mut LeanObject,
    mut v_b_5736_: *mut LeanObject,
    mut v___y_5737_: *mut LeanObject,
    mut v___y_5738_: *mut LeanObject,
    mut v___y_5739_: *mut LeanObject,
    mut v___y_5740_: *mut LeanObject,
    mut v___y_5741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5742_: usize = 0;
    let mut v_i_boxed_5743_: usize = 0;
    let mut v_res_5744_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5742_ = lean_unbox_usize(v_sz_5734_);
    lean_dec(v_sz_5734_);
    v_i_boxed_5743_ = lean_unbox_usize(v_i_5735_);
    lean_dec(v_i_5735_);
    v_res_5744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_5733_, v_sz_boxed_5742_, v_i_boxed_5743_, v_b_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
    lean_dec(v___y_5740_);
    lean_dec_ref(v___y_5739_);
    lean_dec(v___y_5738_);
    lean_dec_ref(v___y_5737_);
    lean_dec_ref(v_as_5733_);
    return v_res_5744_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(
    mut v_msg_5745_: *mut LeanObject,
    mut v___y_5746_: *mut LeanObject,
    mut v___y_5747_: *mut LeanObject,
    mut v___y_5748_: *mut LeanObject,
    mut v___y_5749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724__overap_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    v___f_5751_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0;
    v___x_1724__overap_5752_ = lean_panic_fn_borrowed(v___f_5751_, v_msg_5745_);
    lean_inc(v___y_5749_);
    lean_inc_ref(v___y_5748_);
    lean_inc(v___y_5747_);
    lean_inc_ref(v___y_5746_);
    v___x_5753_ = lean_apply_5(
        v___x_1724__overap_5752_,
        v___y_5746_,
        v___y_5747_,
        v___y_5748_,
        v___y_5749_,
        lean_box(0),
    );
    return v___x_5753_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(
    mut v_msg_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
    mut v___y_5758_: *mut LeanObject,
    mut v___y_5759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5760_: *mut LeanObject = core::ptr::null_mut();
    v_res_5760_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(
        v_msg_5754_,
        v___y_5755_,
        v___y_5756_,
        v___y_5757_,
        v___y_5758_,
    );
    lean_dec(v___y_5758_);
    lean_dec_ref(v___y_5757_);
    lean_dec(v___y_5756_);
    lean_dec_ref(v___y_5755_);
    return v_res_5760_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0()
-> f64 {
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: f64 = 0.0;
    v___x_5761_ = lean_unsigned_to_nat(0);
    v___x_5762_ = lean_float_of_nat(v___x_5761_);
    return v___x_5762_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(
    mut v_cls_5766_: *mut LeanObject,
    mut v_msg_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5778_: u8 = 0;
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5791_: u8 = 0;
    let mut v_tid_5792_: u64 = 0;
    let mut v_traces_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5796_: u8 = 0;
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: f64 = 0.0;
    let mut v___x_5799_: u8 = 0;
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5817_: u8 = 0;
    let mut v_isSharedCheck_5818_: u8 = 0;
    let mut v_isSharedCheck_5819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5773_ = lean_ctor_get(v___y_5770_, 5);
                v___x_5774_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_);
                v_a_5775_ = lean_ctor_get(v___x_5774_, 0);
                v_isSharedCheck_5819_ = (!lean_is_exclusive(v___x_5774_)) as u8;
                if v_isSharedCheck_5819_ == 0 {
                    v___x_5777_ = v___x_5774_;
                    v_isShared_5778_ = v_isSharedCheck_5819_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5775_);
                    lean_dec(v___x_5774_);
                    v___x_5777_ = lean_box(0);
                    v_isShared_5778_ = v_isSharedCheck_5819_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5779_ = lean_st_ref_take(v___y_5771_);
                v_traceState_5780_ = lean_ctor_get(v___x_5779_, 4);
                v_env_5781_ = lean_ctor_get(v___x_5779_, 0);
                v_nextMacroScope_5782_ = lean_ctor_get(v___x_5779_, 1);
                v_ngen_5783_ = lean_ctor_get(v___x_5779_, 2);
                v_auxDeclNGen_5784_ = lean_ctor_get(v___x_5779_, 3);
                v_cache_5785_ = lean_ctor_get(v___x_5779_, 5);
                v_messages_5786_ = lean_ctor_get(v___x_5779_, 6);
                v_infoState_5787_ = lean_ctor_get(v___x_5779_, 7);
                v_snapshotTasks_5788_ = lean_ctor_get(v___x_5779_, 8);
                v_isSharedCheck_5818_ = (!lean_is_exclusive(v___x_5779_)) as u8;
                if v_isSharedCheck_5818_ == 0 {
                    v___x_5790_ = v___x_5779_;
                    v_isShared_5791_ = v_isSharedCheck_5818_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5788_);
                    lean_inc(v_infoState_5787_);
                    lean_inc(v_messages_5786_);
                    lean_inc(v_cache_5785_);
                    lean_inc(v_traceState_5780_);
                    lean_inc(v_auxDeclNGen_5784_);
                    lean_inc(v_ngen_5783_);
                    lean_inc(v_nextMacroScope_5782_);
                    lean_inc(v_env_5781_);
                    lean_dec(v___x_5779_);
                    v___x_5790_ = lean_box(0);
                    v_isShared_5791_ = v_isSharedCheck_5818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5792_ = lean_ctor_get_uint64(
                    v_traceState_5780_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5793_ = lean_ctor_get(v_traceState_5780_, 0);
                v_isSharedCheck_5817_ = (!lean_is_exclusive(v_traceState_5780_)) as u8;
                if v_isSharedCheck_5817_ == 0 {
                    v___x_5795_ = v_traceState_5780_;
                    v_isShared_5796_ = v_isSharedCheck_5817_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_5793_);
                    lean_dec(v_traceState_5780_);
                    v___x_5795_ = lean_box(0);
                    v_isShared_5796_ = v_isSharedCheck_5817_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5797_ = lean_box(0);
                v___x_5798_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
                v___x_5799_ = 0;
                v___x_5800_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1;
                v___x_5801_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_5801_, 0, v_cls_5766_);
                lean_ctor_set(v___x_5801_, 1, v___x_5797_);
                lean_ctor_set(v___x_5801_, 2, v___x_5800_);
                lean_ctor_set_float(
                    v___x_5801_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5798_,
                );
                lean_ctor_set_float(
                    v___x_5801_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5798_,
                );
                lean_ctor_set_uint8(
                    v___x_5801_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_5799_,
                );
                v___x_5802_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2;
                v___x_5803_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5803_, 0, v___x_5801_);
                lean_ctor_set(v___x_5803_, 1, v_a_5775_);
                lean_ctor_set(v___x_5803_, 2, v___x_5802_);
                lean_inc(v_ref_5773_);
                v___x_5804_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5804_, 0, v_ref_5773_);
                lean_ctor_set(v___x_5804_, 1, v___x_5803_);
                v___x_5805_ = l_Lean_PersistentArray_push___redArg(v_traces_5793_, v___x_5804_);
                if v_isShared_5796_ == 0 {
                    lean_ctor_set(v___x_5795_, 0, v___x_5805_);
                    v___x_5807_ = v___x_5795_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5805_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5816_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5792_,
                    );
                    v___x_5807_ = v_reuseFailAlloc_5816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5791_ == 0 {
                    lean_ctor_set(v___x_5790_, 4, v___x_5807_);
                    v___x_5809_ = v___x_5790_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_env_5781_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 1, v_nextMacroScope_5782_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 2, v_ngen_5783_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 3, v_auxDeclNGen_5784_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 4, v___x_5807_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 5, v_cache_5785_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 6, v_messages_5786_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 7, v_infoState_5787_);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 8, v_snapshotTasks_5788_);
                    v___x_5809_ = v_reuseFailAlloc_5815_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5810_ = lean_st_ref_set(v___y_5771_, v___x_5809_);
                v___x_5811_ = lean_box(0);
                if v_isShared_5778_ == 0 {
                    lean_ctor_set(v___x_5777_, 0, v___x_5811_);
                    v___x_5813_ = v___x_5777_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5814_, 0, v___x_5811_);
                    v___x_5813_ = v_reuseFailAlloc_5814_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(
    mut v_cls_5820_: *mut LeanObject,
    mut v_msg_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5827_: *mut LeanObject = core::ptr::null_mut();
    v_res_5827_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(
        v_cls_5820_,
        v_msg_5821_,
        v___y_5822_,
        v___y_5823_,
        v___y_5824_,
        v___y_5825_,
    );
    lean_dec(v___y_5825_);
    lean_dec_ref(v___y_5824_);
    lean_dec(v___y_5823_);
    lean_dec_ref(v___y_5822_);
    return v_res_5827_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    v___x_5830_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1;
    v___x_5831_ = lean_unsigned_to_nat(8);
    v___x_5832_ = lean_unsigned_to_nat(135);
    v___x_5833_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0;
    v___x_5834_ = l_Lean_Elab_WF_packCalls___lam__2___closed__0;
    v___x_5835_ = l_mkPanicMessageWithDecl(
        v___x_5834_,
        v___x_5833_,
        v___x_5832_,
        v___x_5831_,
        v___x_5830_,
    );
    return v___x_5835_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(
    mut v___x_5836_: *mut LeanObject,
    mut v_unaryPreDefNonRec_5837_: *mut LeanObject,
    mut v___x_5838_: *mut LeanObject,
    mut v_us_5839_: *mut LeanObject,
    mut v_argsPacker_5840_: *mut LeanObject,
    mut v_j_5841_: *mut LeanObject,
    mut v_isZero_5842_: u8,
    mut v_params_5843_: *mut LeanObject,
    mut v_x_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
    mut v___y_5847_: *mut LeanObject,
    mut v___y_5848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: u8 = 0;
    v___x_5850_ = lean_array_get_size(v_params_5843_);
    v___x_5851_ = lean_nat_dec_eq(v___x_5836_, v___x_5850_);
    if v___x_5851_ == 0 {
        let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_j_5841_);
        lean_dec(v_us_5839_);
        lean_dec_ref(v_unaryPreDefNonRec_5837_);
        v___x_5852_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
        v___x_5853_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(
            v___x_5852_,
            v___y_5845_,
            v___y_5846_,
            v___y_5847_,
            v___y_5848_,
        );
        return v___x_5853_;
    } else {
        let mut v_declName_5854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
        v_declName_5854_ = lean_ctor_get(v_unaryPreDefNonRec_5837_, 3);
        lean_inc(v_declName_5854_);
        lean_dec_ref(v_unaryPreDefNonRec_5837_);
        v___x_5855_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_5838_, v_params_5843_);
        v___x_5856_ = l_Lean_mkConst(v_declName_5854_, v_us_5839_);
        v___x_5857_ = l_Lean_mkAppN(v___x_5856_, v___x_5855_);
        lean_dec_ref(v___x_5855_);
        v___x_5858_ = l_Lean_Meta_ArgsPacker_curryProj(
            v_argsPacker_5840_,
            v___x_5857_,
            v_j_5841_,
            v___y_5845_,
            v___y_5846_,
            v___y_5847_,
            v___y_5848_,
        );
        if lean_obj_tag(v___x_5858_) == 0 {
            let mut v_a_5859_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5862_: u8 = 0;
            let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
            v_a_5859_ = lean_ctor_get(v___x_5858_, 0);
            lean_inc(v_a_5859_);
            lean_dec_ref_known(v___x_5858_, 1);
            v___x_5860_ =
                l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_5838_, v_params_5843_);
            v___x_5861_ = l_Lean_Expr_beta(v_a_5859_, v___x_5860_);
            v___x_5862_ = 1;
            v___x_5863_ = l_Lean_Meta_mkLambdaFVars(
                v_params_5843_,
                v___x_5861_,
                v_isZero_5842_,
                v___x_5851_,
                v_isZero_5842_,
                v___x_5851_,
                v___x_5862_,
                v___y_5845_,
                v___y_5846_,
                v___y_5847_,
                v___y_5848_,
            );
            return v___x_5863_;
        } else {
            return v___x_5858_;
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(
    mut v___x_5864_: *mut LeanObject,
    mut v_unaryPreDefNonRec_5865_: *mut LeanObject,
    mut v___x_5866_: *mut LeanObject,
    mut v_us_5867_: *mut LeanObject,
    mut v_argsPacker_5868_: *mut LeanObject,
    mut v_j_5869_: *mut LeanObject,
    mut v_isZero_5870_: *mut LeanObject,
    mut v_params_5871_: *mut LeanObject,
    mut v_x_5872_: *mut LeanObject,
    mut v___y_5873_: *mut LeanObject,
    mut v___y_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
    mut v___y_5877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_5878_: u8 = 0;
    let mut v_res_5879_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5878_ = (lean_unbox(v_isZero_5870_) as u8);
    v_res_5879_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_5864_, v_unaryPreDefNonRec_5865_, v___x_5866_, v_us_5867_, v_argsPacker_5868_, v_j_5869_, v_isZero_boxed_5878_, v_params_5871_, v_x_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
    lean_dec(v___y_5876_);
    lean_dec_ref(v___y_5875_);
    lean_dec(v___y_5874_);
    lean_dec_ref(v___y_5873_);
    lean_dec_ref(v_x_5872_);
    lean_dec_ref(v_params_5871_);
    lean_dec_ref(v_argsPacker_5868_);
    lean_dec_ref(v___x_5866_);
    lean_dec(v___x_5864_);
    return v_res_5879_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    v___x_5890_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3;
    v___x_5891_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5;
    v___x_5892_ = l_Lean_Name_append(v___x_5891_, v___x_5890_);
    return v___x_5892_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    v___x_5894_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7;
    v___x_5895_ = l_Lean_stringToMessageData(v___x_5894_);
    return v___x_5895_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(
    mut v_fixedParamPerms_5896_: *mut LeanObject,
    mut v_unaryPreDefNonRec_5897_: *mut LeanObject,
    mut v_us_5898_: *mut LeanObject,
    mut v_argsPacker_5899_: *mut LeanObject,
    mut v_as_5900_: *mut LeanObject,
    mut v_i_5901_: *mut LeanObject,
    mut v_j_5902_: *mut LeanObject,
    mut v_bs_5903_: *mut LeanObject,
    mut v___y_5904_: *mut LeanObject,
    mut v___y_5905_: *mut LeanObject,
    mut v___y_5906_: *mut LeanObject,
    mut v___y_5907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5910_: u8 = 0;
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5915_: u8 = 0;
    let mut v_levelParams_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termination_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5925_: u8 = 0;
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5936_: u8 = 0;
    let mut v_one_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: u8 = 0;
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut v_a_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5966_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5970_: u8 = 0;
    let mut v_isSharedCheck_5971_: u8 = 0;
    let mut v_unused_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5909_ = lean_unsigned_to_nat(0);
                v_isZero_5910_ = lean_nat_dec_eq(v_i_5901_, v_zero_5909_);
                if v_isZero_5910_ == 1 {
                    lean_dec(v_j_5902_);
                    lean_dec(v_i_5901_);
                    lean_dec_ref(v_argsPacker_5899_);
                    lean_dec(v_us_5898_);
                    lean_dec_ref(v_unaryPreDefNonRec_5897_);
                    v___x_5911_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5911_, 0, v_bs_5903_);
                    return v___x_5911_;
                } else {
                    v_perms_5912_ = lean_ctor_get(v_fixedParamPerms_5896_, 1);
                    v___x_5913_ = lean_array_fget(v_as_5900_, v_j_5902_);
                    v_ref_5914_ = lean_ctor_get(v___x_5913_, 0);
                    v_kind_5915_ = lean_ctor_get_uint8(
                        v___x_5913_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    );
                    v_levelParams_5916_ = lean_ctor_get(v___x_5913_, 1);
                    v_modifiers_5917_ = lean_ctor_get(v___x_5913_, 2);
                    v_declName_5918_ = lean_ctor_get(v___x_5913_, 3);
                    v_binders_5919_ = lean_ctor_get(v___x_5913_, 4);
                    v_numSectionVars_5920_ = lean_ctor_get(v___x_5913_, 5);
                    v_type_5921_ = lean_ctor_get(v___x_5913_, 6);
                    v_termination_5922_ = lean_ctor_get(v___x_5913_, 8);
                    v_isSharedCheck_5971_ = (!lean_is_exclusive(v___x_5913_)) as u8;
                    if v_isSharedCheck_5971_ == 0 {
                        v_unused_5972_ = lean_ctor_get(v___x_5913_, 7);
                        lean_dec(v_unused_5972_);
                        v___x_5924_ = v___x_5913_;
                        v_isShared_5925_ = v_isSharedCheck_5971_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_termination_5922_);
                        lean_inc(v_type_5921_);
                        lean_inc(v_numSectionVars_5920_);
                        lean_inc(v_binders_5919_);
                        lean_inc(v_declName_5918_);
                        lean_inc(v_modifiers_5917_);
                        lean_inc(v_levelParams_5916_);
                        lean_inc(v_ref_5914_);
                        lean_dec(v___x_5913_);
                        v___x_5924_ = lean_box(0);
                        v_isShared_5925_ = v_isSharedCheck_5971_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5926_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Elab_WF_packCalls___lam__2___closed__4_once),
                    _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4,
                );
                v___x_5927_ = lean_array_get_borrowed(v___x_5926_, v_perms_5912_, v_j_5902_);
                v___x_5928_ = lean_array_get_size(v___x_5927_);
                v___x_5929_ = lean_box((v_isZero_5910_) as usize);
                lean_inc(v_j_5902_);
                lean_inc_ref(v_argsPacker_5899_);
                lean_inc(v_us_5898_);
                lean_inc(v___x_5927_);
                lean_inc_ref(v_unaryPreDefNonRec_5897_);
                v___f_5930_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                lean_closure_set(v___f_5930_, 0, v___x_5928_);
                lean_closure_set(v___f_5930_, 1, v_unaryPreDefNonRec_5897_);
                lean_closure_set(v___f_5930_, 2, v___x_5927_);
                lean_closure_set(v___f_5930_, 3, v_us_5898_);
                lean_closure_set(v___f_5930_, 4, v_argsPacker_5899_);
                lean_closure_set(v___f_5930_, 5, v_j_5902_);
                lean_closure_set(v___f_5930_, 6, v___x_5929_);
                v___x_5931_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5931_, 0, v___x_5928_);
                lean_inc_ref(v_type_5921_);
                v___x_5932_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_5921_, v___x_5931_, v___f_5930_, v_isZero_5910_, v_isZero_5910_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
                if lean_obj_tag(v___x_5932_) == 0 {
                    v_options_5933_ = lean_ctor_get(v___y_5906_, 2);
                    v_a_5934_ = lean_ctor_get(v___x_5932_, 0);
                    lean_inc(v_a_5934_);
                    lean_dec_ref_known(v___x_5932_, 1);
                    v_inheritedTraceOptions_5935_ = lean_ctor_get(v___y_5906_, 13);
                    v_hasTrace_5936_ = lean_ctor_get_uint8(
                        v_options_5933_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_one_5937_ = lean_unsigned_to_nat(1);
                    v_n_5938_ = lean_nat_sub(v_i_5901_, v_one_5937_);
                    lean_dec(v_i_5901_);
                    if v_hasTrace_5936_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_5946_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3;
                        v___x_5947_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
                        v___x_5948_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5935_,
                            v_options_5933_,
                            v___x_5947_,
                        );
                        if v___x_5948_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_declName_5918_);
                            v___x_5949_ = l_Lean_MessageData_ofName(v_declName_5918_);
                            v___x_5950_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
                            v___x_5951_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5951_, 0, v___x_5949_);
                            lean_ctor_set(v___x_5951_, 1, v___x_5950_);
                            lean_inc(v_a_5934_);
                            v___x_5952_ = l_Lean_MessageData_ofExpr(v_a_5934_);
                            v___x_5953_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5953_, 0, v___x_5951_);
                            lean_ctor_set(v___x_5953_, 1, v___x_5952_);
                            v___x_5954_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_5946_, v___x_5953_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
                            if lean_obj_tag(v___x_5954_) == 0 {
                                lean_dec_ref_known(v___x_5954_, 1);
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_n_5938_);
                                lean_dec(v_a_5934_);
                                lean_del_object(v___x_5924_);
                                lean_dec_ref(v_termination_5922_);
                                lean_dec_ref(v_type_5921_);
                                lean_dec(v_numSectionVars_5920_);
                                lean_dec(v_binders_5919_);
                                lean_dec(v_declName_5918_);
                                lean_dec_ref(v_modifiers_5917_);
                                lean_dec(v_levelParams_5916_);
                                lean_dec(v_ref_5914_);
                                lean_dec_ref(v_bs_5903_);
                                lean_dec(v_j_5902_);
                                lean_dec_ref(v_argsPacker_5899_);
                                lean_dec(v_us_5898_);
                                lean_dec_ref(v_unaryPreDefNonRec_5897_);
                                v_a_5955_ = lean_ctor_get(v___x_5954_, 0);
                                v_isSharedCheck_5962_ = (!lean_is_exclusive(v___x_5954_)) as u8;
                                if v_isSharedCheck_5962_ == 0 {
                                    v___x_5957_ = v___x_5954_;
                                    v_isShared_5958_ = v_isSharedCheck_5962_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_5955_);
                                    lean_dec(v___x_5954_);
                                    v___x_5957_ = lean_box(0);
                                    v_isShared_5958_ = v_isSharedCheck_5962_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5924_);
                    lean_dec_ref(v_termination_5922_);
                    lean_dec_ref(v_type_5921_);
                    lean_dec(v_numSectionVars_5920_);
                    lean_dec(v_binders_5919_);
                    lean_dec(v_declName_5918_);
                    lean_dec_ref(v_modifiers_5917_);
                    lean_dec(v_levelParams_5916_);
                    lean_dec(v_ref_5914_);
                    lean_dec_ref(v_bs_5903_);
                    lean_dec(v_j_5902_);
                    lean_dec(v_i_5901_);
                    lean_dec_ref(v_argsPacker_5899_);
                    lean_dec(v_us_5898_);
                    lean_dec_ref(v_unaryPreDefNonRec_5897_);
                    v_a_5963_ = lean_ctor_get(v___x_5932_, 0);
                    v_isSharedCheck_5970_ = (!lean_is_exclusive(v___x_5932_)) as u8;
                    if v_isSharedCheck_5970_ == 0 {
                        v___x_5965_ = v___x_5932_;
                        v_isShared_5966_ = v_isSharedCheck_5970_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5963_);
                        lean_dec(v___x_5932_);
                        v___x_5965_ = lean_box(0);
                        v_isShared_5966_ = v_isSharedCheck_5970_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5925_ == 0 {
                    lean_ctor_set(v___x_5924_, 7, v_a_5934_);
                    v___x_5941_ = v___x_5924_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 9, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_ref_5914_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 1, v_levelParams_5916_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 2, v_modifiers_5917_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 3, v_declName_5918_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 4, v_binders_5919_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 5, v_numSectionVars_5920_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 6, v_type_5921_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 7, v_a_5934_);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 8, v_termination_5922_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5945_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        v_kind_5915_,
                    );
                    v___x_5941_ = v_reuseFailAlloc_5945_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5942_ = lean_nat_add(v_j_5902_, v_one_5937_);
                lean_dec(v_j_5902_);
                v___x_5943_ = lean_array_push(v_bs_5903_, v___x_5941_);
                v_i_5901_ = v_n_5938_;
                v_j_5902_ = v___x_5942_;
                v_bs_5903_ = v___x_5943_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_5958_ == 0 {
                    v___x_5960_ = v___x_5957_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_a_5955_);
                    v___x_5960_ = v_reuseFailAlloc_5961_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5960_;
            }
            6 => {
                if v_isShared_5966_ == 0 {
                    v___x_5968_ = v___x_5965_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
                    v___x_5968_ = v_reuseFailAlloc_5969_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(
    mut v_fixedParamPerms_5973_: *mut LeanObject,
    mut v_unaryPreDefNonRec_5974_: *mut LeanObject,
    mut v_us_5975_: *mut LeanObject,
    mut v_argsPacker_5976_: *mut LeanObject,
    mut v_as_5977_: *mut LeanObject,
    mut v_i_5978_: *mut LeanObject,
    mut v_j_5979_: *mut LeanObject,
    mut v_bs_5980_: *mut LeanObject,
    mut v___y_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
    mut v___y_5985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5986_: *mut LeanObject = core::ptr::null_mut();
    v_res_5986_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(
            v_fixedParamPerms_5973_,
            v_unaryPreDefNonRec_5974_,
            v_us_5975_,
            v_argsPacker_5976_,
            v_as_5977_,
            v_i_5978_,
            v_j_5979_,
            v_bs_5980_,
            v___y_5981_,
            v___y_5982_,
            v___y_5983_,
            v___y_5984_,
        );
    lean_dec(v___y_5984_);
    lean_dec_ref(v___y_5983_);
    lean_dec(v___y_5982_);
    lean_dec_ref(v___y_5981_);
    lean_dec_ref(v_as_5977_);
    lean_dec_ref(v_fixedParamPerms_5973_);
    return v_res_5986_;
}
pub unsafe fn l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(
    mut v_unaryPreDefNonRec_5987_: *mut LeanObject,
    mut v_preDefs_5988_: *mut LeanObject,
    mut v_fixedParamPerms_5989_: *mut LeanObject,
    mut v_us_5990_: *mut LeanObject,
    mut v_argsPacker_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6005_: u8 = 0;
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5997_ = l_Lean_Elab_addAsAxiom___redArg(
                    v_unaryPreDefNonRec_5987_,
                    v___y_5994_,
                    v___y_5995_,
                );
                if lean_obj_tag(v___x_5997_) == 0 {
                    lean_dec_ref_known(v___x_5997_, 1);
                    v___x_5998_ = lean_array_get_size(v_preDefs_5988_);
                    v___x_5999_ = lean_unsigned_to_nat(0);
                    v___x_6000_ = lean_mk_empty_array_with_capacity(v___x_5998_);
                    v___x_6001_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_5989_, v_unaryPreDefNonRec_5987_, v_us_5990_, v_argsPacker_5991_, v_preDefs_5988_, v___x_5998_, v___x_5999_, v___x_6000_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
                    return v___x_6001_;
                } else {
                    lean_dec_ref(v_argsPacker_5991_);
                    lean_dec(v_us_5990_);
                    lean_dec_ref(v_unaryPreDefNonRec_5987_);
                    v_a_6002_ = lean_ctor_get(v___x_5997_, 0);
                    v_isSharedCheck_6009_ = (!lean_is_exclusive(v___x_5997_)) as u8;
                    if v_isSharedCheck_6009_ == 0 {
                        v___x_6004_ = v___x_5997_;
                        v_isShared_6005_ = v_isSharedCheck_6009_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6002_);
                        lean_dec(v___x_5997_);
                        v___x_6004_ = lean_box(0);
                        v_isShared_6005_ = v_isSharedCheck_6009_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6005_ == 0 {
                    v___x_6007_ = v___x_6004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_a_6002_);
                    v___x_6007_ = v_reuseFailAlloc_6008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(
    mut v_unaryPreDefNonRec_6010_: *mut LeanObject,
    mut v_preDefs_6011_: *mut LeanObject,
    mut v_fixedParamPerms_6012_: *mut LeanObject,
    mut v_us_6013_: *mut LeanObject,
    mut v_argsPacker_6014_: *mut LeanObject,
    mut v___y_6015_: *mut LeanObject,
    mut v___y_6016_: *mut LeanObject,
    mut v___y_6017_: *mut LeanObject,
    mut v___y_6018_: *mut LeanObject,
    mut v___y_6019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6020_: *mut LeanObject = core::ptr::null_mut();
    v_res_6020_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(
        v_unaryPreDefNonRec_6010_,
        v_preDefs_6011_,
        v_fixedParamPerms_6012_,
        v_us_6013_,
        v_argsPacker_6014_,
        v___y_6015_,
        v___y_6016_,
        v___y_6017_,
        v___y_6018_,
    );
    lean_dec(v___y_6018_);
    lean_dec_ref(v___y_6017_);
    lean_dec(v___y_6016_);
    lean_dec_ref(v___y_6015_);
    lean_dec_ref(v_fixedParamPerms_6012_);
    lean_dec_ref(v_preDefs_6011_);
    return v_res_6020_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    v___x_6021_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6021_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    v___x_6022_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
    v___x_6023_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6023_, 0, v___x_6022_);
    return v___x_6023_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    v___x_6024_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
    v___x_6025_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6025_, 0, v___x_6024_);
    lean_ctor_set(v___x_6025_, 1, v___x_6024_);
    return v___x_6025_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    v___x_6026_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
    v___x_6027_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_6027_, 0, v___x_6026_);
    lean_ctor_set(v___x_6027_, 1, v___x_6026_);
    lean_ctor_set(v___x_6027_, 2, v___x_6026_);
    lean_ctor_set(v___x_6027_, 3, v___x_6026_);
    lean_ctor_set(v___x_6027_, 4, v___x_6026_);
    lean_ctor_set(v___x_6027_, 5, v___x_6026_);
    return v___x_6027_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(
    mut v_env_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6042_: u8 = 0;
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6062_: u8 = 0;
    let mut v_unused_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v_unused_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6032_ = lean_st_ref_take(v___y_6030_);
                v_nextMacroScope_6033_ = lean_ctor_get(v___x_6032_, 1);
                v_ngen_6034_ = lean_ctor_get(v___x_6032_, 2);
                v_auxDeclNGen_6035_ = lean_ctor_get(v___x_6032_, 3);
                v_traceState_6036_ = lean_ctor_get(v___x_6032_, 4);
                v_messages_6037_ = lean_ctor_get(v___x_6032_, 6);
                v_infoState_6038_ = lean_ctor_get(v___x_6032_, 7);
                v_snapshotTasks_6039_ = lean_ctor_get(v___x_6032_, 8);
                v_isSharedCheck_6065_ = (!lean_is_exclusive(v___x_6032_)) as u8;
                if v_isSharedCheck_6065_ == 0 {
                    v_unused_6066_ = lean_ctor_get(v___x_6032_, 5);
                    lean_dec(v_unused_6066_);
                    v_unused_6067_ = lean_ctor_get(v___x_6032_, 0);
                    lean_dec(v_unused_6067_);
                    v___x_6041_ = v___x_6032_;
                    v_isShared_6042_ = v_isSharedCheck_6065_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6039_);
                    lean_inc(v_infoState_6038_);
                    lean_inc(v_messages_6037_);
                    lean_inc(v_traceState_6036_);
                    lean_inc(v_auxDeclNGen_6035_);
                    lean_inc(v_ngen_6034_);
                    lean_inc(v_nextMacroScope_6033_);
                    lean_dec(v___x_6032_);
                    v___x_6041_ = lean_box(0);
                    v_isShared_6042_ = v_isSharedCheck_6065_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6043_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
                if v_isShared_6042_ == 0 {
                    lean_ctor_set(v___x_6041_, 5, v___x_6043_);
                    lean_ctor_set(v___x_6041_, 0, v_env_6028_);
                    v___x_6045_ = v___x_6041_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_env_6028_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 1, v_nextMacroScope_6033_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 2, v_ngen_6034_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 3, v_auxDeclNGen_6035_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 4, v_traceState_6036_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 5, v___x_6043_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 6, v_messages_6037_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 7, v_infoState_6038_);
                    lean_ctor_set(v_reuseFailAlloc_6064_, 8, v_snapshotTasks_6039_);
                    v___x_6045_ = v_reuseFailAlloc_6064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6046_ = lean_st_ref_set(v___y_6030_, v___x_6045_);
                v___x_6047_ = lean_st_ref_take(v___y_6029_);
                v_mctx_6048_ = lean_ctor_get(v___x_6047_, 0);
                v_zetaDeltaFVarIds_6049_ = lean_ctor_get(v___x_6047_, 2);
                v_postponed_6050_ = lean_ctor_get(v___x_6047_, 3);
                v_diag_6051_ = lean_ctor_get(v___x_6047_, 4);
                v_isSharedCheck_6062_ = (!lean_is_exclusive(v___x_6047_)) as u8;
                if v_isSharedCheck_6062_ == 0 {
                    v_unused_6063_ = lean_ctor_get(v___x_6047_, 1);
                    lean_dec(v_unused_6063_);
                    v___x_6053_ = v___x_6047_;
                    v_isShared_6054_ = v_isSharedCheck_6062_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_6051_);
                    lean_inc(v_postponed_6050_);
                    lean_inc(v_zetaDeltaFVarIds_6049_);
                    lean_inc(v_mctx_6048_);
                    lean_dec(v___x_6047_);
                    v___x_6053_ = lean_box(0);
                    v_isShared_6054_ = v_isSharedCheck_6062_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6055_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
                if v_isShared_6054_ == 0 {
                    lean_ctor_set(v___x_6053_, 1, v___x_6055_);
                    v___x_6057_ = v___x_6053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6061_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6061_, 0, v_mctx_6048_);
                    lean_ctor_set(v_reuseFailAlloc_6061_, 1, v___x_6055_);
                    lean_ctor_set(v_reuseFailAlloc_6061_, 2, v_zetaDeltaFVarIds_6049_);
                    lean_ctor_set(v_reuseFailAlloc_6061_, 3, v_postponed_6050_);
                    lean_ctor_set(v_reuseFailAlloc_6061_, 4, v_diag_6051_);
                    v___x_6057_ = v_reuseFailAlloc_6061_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6058_ = lean_st_ref_set(v___y_6029_, v___x_6057_);
                v___x_6059_ = lean_box(0);
                v___x_6060_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6060_, 0, v___x_6059_);
                return v___x_6060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(
    mut v_env_6068_: *mut LeanObject,
    mut v___y_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6072_: *mut LeanObject = core::ptr::null_mut();
    v_res_6072_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_6068_, v___y_6069_, v___y_6070_);
    lean_dec(v___y_6070_);
    lean_dec(v___y_6069_);
    return v_res_6072_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(
    mut v_env_6073_: *mut LeanObject,
    mut v_x_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
    mut v___y_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6087_: u8 = 0;
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6091_: u8 = 0;
    let mut v_unused_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6099_: u8 = 0;
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6103_: u8 = 0;
    let mut v_unused_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6080_ = lean_st_ref_get(v___y_6078_);
                v_env_6081_ = lean_ctor_get(v___x_6080_, 0);
                lean_inc_ref(v_env_6081_);
                lean_dec(v___x_6080_);
                v___x_6093_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_6073_, v___y_6076_, v___y_6078_);
                lean_dec_ref(v___x_6093_);
                lean_inc(v___y_6078_);
                lean_inc_ref(v___y_6077_);
                lean_inc(v___y_6076_);
                lean_inc_ref(v___y_6075_);
                v___x_6094_ = lean_apply_5(
                    v_x_6074_,
                    v___y_6075_,
                    v___y_6076_,
                    v___y_6077_,
                    v___y_6078_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6094_) == 0 {
                    v_a_6095_ = lean_ctor_get(v___x_6094_, 0);
                    lean_inc(v_a_6095_);
                    lean_dec_ref_known(v___x_6094_, 1);
                    v___x_6096_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_6081_, v___y_6076_, v___y_6078_);
                    v_isSharedCheck_6103_ = (!lean_is_exclusive(v___x_6096_)) as u8;
                    if v_isSharedCheck_6103_ == 0 {
                        v_unused_6104_ = lean_ctor_get(v___x_6096_, 0);
                        lean_dec(v_unused_6104_);
                        v___x_6098_ = v___x_6096_;
                        v_isShared_6099_ = v_isSharedCheck_6103_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_6096_);
                        v___x_6098_ = lean_box(0);
                        v_isShared_6099_ = v_isSharedCheck_6103_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6105_ = lean_ctor_get(v___x_6094_, 0);
                    lean_inc(v_a_6105_);
                    lean_dec_ref_known(v___x_6094_, 1);
                    v_a_6083_ = v_a_6105_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6084_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_6081_, v___y_6076_, v___y_6078_);
                v_isSharedCheck_6091_ = (!lean_is_exclusive(v___x_6084_)) as u8;
                if v_isSharedCheck_6091_ == 0 {
                    v_unused_6092_ = lean_ctor_get(v___x_6084_, 0);
                    lean_dec(v_unused_6092_);
                    v___x_6086_ = v___x_6084_;
                    v_isShared_6087_ = v_isSharedCheck_6091_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_6084_);
                    v___x_6086_ = lean_box(0);
                    v_isShared_6087_ = v_isSharedCheck_6091_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6087_ == 0 {
                    lean_ctor_set_tag(v___x_6086_, 1);
                    lean_ctor_set(v___x_6086_, 0, v_a_6083_);
                    v___x_6089_ = v___x_6086_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6090_, 0, v_a_6083_);
                    v___x_6089_ = v_reuseFailAlloc_6090_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6089_;
            }
            4 => {
                if v_isShared_6099_ == 0 {
                    lean_ctor_set(v___x_6098_, 0, v_a_6095_);
                    v___x_6101_ = v___x_6098_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6102_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6095_);
                    v___x_6101_ = v_reuseFailAlloc_6102_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6101_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(
    mut v_env_6106_: *mut LeanObject,
    mut v_x_6107_: *mut LeanObject,
    mut v___y_6108_: *mut LeanObject,
    mut v___y_6109_: *mut LeanObject,
    mut v___y_6110_: *mut LeanObject,
    mut v___y_6111_: *mut LeanObject,
    mut v___y_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6113_: *mut LeanObject = core::ptr::null_mut();
    v_res_6113_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(
        v_env_6106_,
        v_x_6107_,
        v___y_6108_,
        v___y_6109_,
        v___y_6110_,
        v___y_6111_,
    );
    lean_dec(v___y_6111_);
    lean_dec_ref(v___y_6110_);
    lean_dec(v___y_6109_);
    lean_dec_ref(v___y_6108_);
    return v_res_6113_;
}
pub unsafe fn l_Lean_Elab_WF_preDefsFromUnaryNonRec(
    mut v_fixedParamPerms_6114_: *mut LeanObject,
    mut v_argsPacker_6115_: *mut LeanObject,
    mut v_preDefs_6116_: *mut LeanObject,
    mut v_unaryPreDefNonRec_6117_: *mut LeanObject,
    mut v_a_6118_: *mut LeanObject,
    mut v_a_6119_: *mut LeanObject,
    mut v_a_6120_: *mut LeanObject,
    mut v_a_6121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    v___x_6123_ = lean_st_ref_get(v_a_6121_);
    v_levelParams_6124_ = lean_ctor_get(v_unaryPreDefNonRec_6117_, 1);
    v_env_6125_ = lean_ctor_get(v___x_6123_, 0);
    lean_inc_ref(v_env_6125_);
    lean_dec(v___x_6123_);
    v___x_6126_ = lean_box(0);
    lean_inc(v_levelParams_6124_);
    v_us_6127_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(
        v_levelParams_6124_,
        v___x_6126_,
    );
    v___f_6128_ = lean_alloc_closure(
        l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___f_6128_, 0, v_unaryPreDefNonRec_6117_);
    lean_closure_set(v___f_6128_, 1, v_preDefs_6116_);
    lean_closure_set(v___f_6128_, 2, v_fixedParamPerms_6114_);
    lean_closure_set(v___f_6128_, 3, v_us_6127_);
    lean_closure_set(v___f_6128_, 4, v_argsPacker_6115_);
    v___x_6129_ = l_Lean_Environment_unlockAsync(v_env_6125_);
    v___x_6130_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(
        v___x_6129_,
        v___f_6128_,
        v_a_6118_,
        v_a_6119_,
        v_a_6120_,
        v_a_6121_,
    );
    return v___x_6130_;
}
pub unsafe fn l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(
    mut v_fixedParamPerms_6131_: *mut LeanObject,
    mut v_argsPacker_6132_: *mut LeanObject,
    mut v_preDefs_6133_: *mut LeanObject,
    mut v_unaryPreDefNonRec_6134_: *mut LeanObject,
    mut v_a_6135_: *mut LeanObject,
    mut v_a_6136_: *mut LeanObject,
    mut v_a_6137_: *mut LeanObject,
    mut v_a_6138_: *mut LeanObject,
    mut v_a_6139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6140_: *mut LeanObject = core::ptr::null_mut();
    v_res_6140_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(
        v_fixedParamPerms_6131_,
        v_argsPacker_6132_,
        v_preDefs_6133_,
        v_unaryPreDefNonRec_6134_,
        v_a_6135_,
        v_a_6136_,
        v_a_6137_,
        v_a_6138_,
    );
    lean_dec(v_a_6138_);
    lean_dec_ref(v_a_6137_);
    lean_dec(v_a_6136_);
    lean_dec_ref(v_a_6135_);
    return v_res_6140_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(
    mut v_fixedParamPerms_6141_: *mut LeanObject,
    mut v_unaryPreDefNonRec_6142_: *mut LeanObject,
    mut v_us_6143_: *mut LeanObject,
    mut v_argsPacker_6144_: *mut LeanObject,
    mut v_as_6145_: *mut LeanObject,
    mut v_i_6146_: *mut LeanObject,
    mut v_j_6147_: *mut LeanObject,
    mut v_inv_6148_: *mut LeanObject,
    mut v_bs_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    v___x_6155_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(
            v_fixedParamPerms_6141_,
            v_unaryPreDefNonRec_6142_,
            v_us_6143_,
            v_argsPacker_6144_,
            v_as_6145_,
            v_i_6146_,
            v_j_6147_,
            v_bs_6149_,
            v___y_6150_,
            v___y_6151_,
            v___y_6152_,
            v___y_6153_,
        );
    return v___x_6155_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(
    mut v_fixedParamPerms_6156_: *mut LeanObject,
    mut v_unaryPreDefNonRec_6157_: *mut LeanObject,
    mut v_us_6158_: *mut LeanObject,
    mut v_argsPacker_6159_: *mut LeanObject,
    mut v_as_6160_: *mut LeanObject,
    mut v_i_6161_: *mut LeanObject,
    mut v_j_6162_: *mut LeanObject,
    mut v_inv_6163_: *mut LeanObject,
    mut v_bs_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
    mut v___y_6168_: *mut LeanObject,
    mut v___y_6169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6170_: *mut LeanObject = core::ptr::null_mut();
    v_res_6170_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(
        v_fixedParamPerms_6156_,
        v_unaryPreDefNonRec_6157_,
        v_us_6158_,
        v_argsPacker_6159_,
        v_as_6160_,
        v_i_6161_,
        v_j_6162_,
        v_inv_6163_,
        v_bs_6164_,
        v___y_6165_,
        v___y_6166_,
        v___y_6167_,
        v___y_6168_,
    );
    lean_dec(v___y_6168_);
    lean_dec_ref(v___y_6167_);
    lean_dec(v___y_6166_);
    lean_dec_ref(v___y_6165_);
    lean_dec_ref(v_as_6160_);
    lean_dec_ref(v_fixedParamPerms_6156_);
    return v_res_6170_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(
    mut v_env_6171_: *mut LeanObject,
    mut v___y_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    v___x_6177_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_6171_, v___y_6173_, v___y_6175_);
    return v___x_6177_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(
    mut v_env_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
    mut v___y_6182_: *mut LeanObject,
    mut v___y_6183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6184_: *mut LeanObject = core::ptr::null_mut();
    v_res_6184_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
    lean_dec(v___y_6182_);
    lean_dec_ref(v___y_6181_);
    lean_dec(v___y_6180_);
    lean_dec_ref(v___y_6179_);
    return v_res_6184_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(
    mut v_00_u03b1_6185_: *mut LeanObject,
    mut v_env_6186_: *mut LeanObject,
    mut v_x_6187_: *mut LeanObject,
    mut v___y_6188_: *mut LeanObject,
    mut v___y_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
    mut v___y_6191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    v___x_6193_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(
        v_env_6186_,
        v_x_6187_,
        v___y_6188_,
        v___y_6189_,
        v___y_6190_,
        v___y_6191_,
    );
    return v___x_6193_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(
    mut v_00_u03b1_6194_: *mut LeanObject,
    mut v_env_6195_: *mut LeanObject,
    mut v_x_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
    mut v___y_6198_: *mut LeanObject,
    mut v___y_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6202_: *mut LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(
        v_00_u03b1_6194_,
        v_env_6195_,
        v_x_6196_,
        v___y_6197_,
        v___y_6198_,
        v___y_6199_,
        v___y_6200_,
    );
    lean_dec(v___y_6200_);
    lean_dec_ref(v___y_6199_);
    lean_dec(v___y_6198_);
    lean_dec_ref(v___y_6197_);
    return v_res_6202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_WF_PackMutual(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_ArgsPacker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
}

// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Theorems
// Imports: Lean.Meta.Sym.Pattern Lean.Meta.DiscrTree Lean.Meta.Sym.Simp.DiscrTree Lean.Meta.AppBuilder Lean.ExtraModUses Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppM, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::DiscrTree::{
    initialize_Lean_Meta_DiscrTree, runtime_initialize_Lean_Meta_DiscrTree,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::Pattern::{
    initialize_Lean_Meta_Sym_Pattern,
    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go,
    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern,
    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern,
    l_Lean_Meta_Sym_instInhabitedPattern_default, runtime_initialize_Lean_Meta_Sym_Pattern,
};
use crate::r#gen::Lean::Meta::Sym::Simp::DiscrTree::{
    initialize_Lean_Meta_Sym_Simp_DiscrTree, l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys,
    l_Lean_Meta_Sym_getMatch___redArg, l_Lean_Meta_Sym_getMatchWithExtra___redArg,
    runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__0_value: LeanStringObject<
    20,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__0_value)
                as *mut LeanObject,
            17542774118954891045 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorem: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instBEqTheorem___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_instBEqTheorem___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_instBEqTheorem___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instBEqTheorem___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instBEqTheorem: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instBEqTheorem___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedTheorems: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__1_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__1_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__0_value) as *mut LeanObject,11870096045526947150 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__4_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 97, 115, 32, 97, 32, 115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 44, 32, 99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 111, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__6_value) as *mut LeanObject,16612019923665488825 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__8_value) as *mut LeanObject,9917798623386220051 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__10_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__10_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__12_value) as *mut LeanObject,907667957179513571 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__0_value) as *mut LeanObject,1953906391527423986 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 111, 112, 101, 120, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__0_value) as *mut LeanObject,12404887534527682101 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__0_value) as *mut LeanObject,12633671826946381106 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__3_value: LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__10_value: LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__14_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__15_value: LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__15_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__17_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_Theorems_insert as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__6_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__6_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__8_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__13_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__13_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__14_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__16_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__18_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__18_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__20_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__21_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__22_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__23_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__23_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__3_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__2()
-> *mut LeanObject {
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2029_ = lean_box(0);
    v___x_2030_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__1;
    v___x_2031_ = l_Lean_Expr_const___override(v___x_2030_, v___x_2029_);
    return v___x_2031_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__3()
-> *mut LeanObject {
    let mut v___x_2032_: u8 = 0;
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v___x_2032_ = 0;
    v___x_2033_ = l_Lean_Meta_Sym_instInhabitedPattern_default;
    v___x_2034_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__2_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__2,
    );
    v___x_2035_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_2035_, 0, v___x_2034_);
    lean_ctor_set(v___x_2035_, 1, v___x_2033_);
    lean_ctor_set(v___x_2035_, 2, v___x_2034_);
    lean_ctor_set_uint8(
        v___x_2035_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2032_,
    );
    return v___x_2035_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default() -> *mut LeanObject {
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    v___x_2036_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__3_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default___closed__3,
    );
    return v___x_2036_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem() -> *mut LeanObject {
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    v___x_2037_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
    return v___x_2037_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instBEqTheorem___lam__0(
    mut v_thm_u2081_2038_: *mut LeanObject,
    mut v_thm_u2082_2039_: *mut LeanObject,
) -> u8 {
    let mut v_expr_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    v_expr_2040_ = lean_ctor_get(v_thm_u2081_2038_, 0);
    v_expr_2041_ = lean_ctor_get(v_thm_u2082_2039_, 0);
    v___x_2042_ = lean_expr_eqv(v_expr_2040_, v_expr_2041_);
    return v___x_2042_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instBEqTheorem___lam__0___boxed(
    mut v_thm_u2081_2043_: *mut LeanObject,
    mut v_thm_u2082_2044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2045_: u8 = 0;
    let mut v_r_2046_: *mut LeanObject = core::ptr::null_mut();
    v_res_2045_ =
        l_Lean_Meta_Sym_Simp_instBEqTheorem___lam__0(v_thm_u2081_2043_, v_thm_u2082_2044_);
    lean_dec_ref(v_thm_u2082_2044_);
    lean_dec_ref(v_thm_u2081_2043_);
    v_r_2046_ = lean_box((v_res_2045_) as usize);
    return v_r_2046_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2049_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1()
-> *mut LeanObject {
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    v___x_2050_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__0_once
        ),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__0,
    );
    v___x_2051_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2051_, 0, v___x_2050_);
    return v___x_2051_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default() -> *mut LeanObject {
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    v___x_2052_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1_once
        ),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1,
    );
    return v___x_2052_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems() -> *mut LeanObject {
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    v___x_2053_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default;
    return v___x_2053_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_keys_2054_: *mut LeanObject,
    mut v_vals_2055_: *mut LeanObject,
    mut v_i_2056_: *mut LeanObject,
    mut v_k_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2058_ = lean_array_get_size(v_keys_2054_);
                v___x_2059_ = lean_nat_dec_lt(v_i_2056_, v___x_2058_);
                if v___x_2059_ == 0 {
                    lean_dec(v_i_2056_);
                    v___x_2060_ = lean_box(0);
                    return v___x_2060_;
                } else {
                    v_k_x27_2061_ = lean_array_fget_borrowed(v_keys_2054_, v_i_2056_);
                    v___x_2062_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_2057_, v_k_x27_2061_);
                    if v___x_2062_ == 0 {
                        v___x_2063_ = lean_unsigned_to_nat(1);
                        v___x_2064_ = lean_nat_add(v_i_2056_, v___x_2063_);
                        lean_dec(v_i_2056_);
                        v_i_2056_ = v___x_2064_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2066_ = lean_array_fget_borrowed(v_vals_2055_, v_i_2056_);
                        lean_dec(v_i_2056_);
                        lean_inc(v___x_2066_);
                        v___x_2067_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2067_, 0, v___x_2066_);
                        return v___x_2067_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_keys_2068_: *mut LeanObject,
    mut v_vals_2069_: *mut LeanObject,
    mut v_i_2070_: *mut LeanObject,
    mut v_k_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2072_: *mut LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_keys_2068_, v_vals_2069_, v_i_2070_, v_k_2071_);
    lean_dec(v_k_2071_);
    lean_dec_ref(v_vals_2069_);
    lean_dec_ref(v_keys_2068_);
    return v_res_2072_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2073_: usize = 0;
    let mut v___x_2074_: usize = 0;
    let mut v___x_2075_: usize = 0;
    v___x_2073_ = 5usize;
    v___x_2074_ = 1usize;
    v___x_2075_ = lean_usize_shift_left(v___x_2074_, v___x_2073_);
    return v___x_2075_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2076_: usize = 0;
    let mut v___x_2077_: usize = 0;
    let mut v___x_2078_: usize = 0;
    v___x_2076_ = 1usize;
    v___x_2077_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__0);
    v___x_2078_ = lean_usize_sub(v___x_2077_, v___x_2076_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2079_: *mut LeanObject,
    mut v_x_2080_: usize,
    mut v_x_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: usize = 0;
    let mut v___x_2085_: usize = 0;
    let mut v___x_2086_: usize = 0;
    let mut v_j_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: usize = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2079_) == 0 {
                    v_es_2082_ = lean_ctor_get(v_x_2079_, 0);
                    v___x_2083_ = lean_box(2);
                    v___x_2084_ = 5usize;
                    v___x_2085_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
                    v___x_2086_ = lean_usize_land(v_x_2080_, v___x_2085_);
                    v_j_2087_ = lean_usize_to_nat(v___x_2086_);
                    v___x_2088_ = lean_array_get_borrowed(v___x_2083_, v_es_2082_, v_j_2087_);
                    lean_dec(v_j_2087_);
                    match lean_obj_tag(v___x_2088_) {
                        0 => {
                            v_key_2089_ = lean_ctor_get(v___x_2088_, 0);
                            v_val_2090_ = lean_ctor_get(v___x_2088_, 1);
                            v___x_2091_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2081_, v_key_2089_);
                            if v___x_2091_ == 0 {
                                v___x_2092_ = lean_box(0);
                                return v___x_2092_;
                            } else {
                                lean_inc(v_val_2090_);
                                v___x_2093_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2093_, 0, v_val_2090_);
                                return v___x_2093_;
                            }
                        }
                        1 => {
                            v_node_2094_ = lean_ctor_get(v___x_2088_, 0);
                            v___x_2095_ = lean_usize_shift_right(v_x_2080_, v___x_2084_);
                            v_x_2079_ = v_node_2094_;
                            v_x_2080_ = v___x_2095_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2097_ = lean_box(0);
                            return v___x_2097_;
                        }
                    }
                } else {
                    v_ks_2098_ = lean_ctor_get(v_x_2079_, 0);
                    v_vs_2099_ = lean_ctor_get(v_x_2079_, 1);
                    v___x_2100_ = lean_unsigned_to_nat(0);
                    v___x_2101_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ks_2098_, v_vs_2099_, v___x_2100_, v_x_2081_);
                    return v___x_2101_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_2102_: *mut LeanObject,
    mut v_x_2103_: *mut LeanObject,
    mut v_x_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1556__boxed_2105_: usize = 0;
    let mut v_res_2106_: *mut LeanObject = core::ptr::null_mut();
    v_x_1556__boxed_2105_ = lean_unbox_usize(v_x_2103_);
    lean_dec(v_x_2103_);
    v_res_2106_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2102_, v_x_1556__boxed_2105_, v_x_2104_);
    lean_dec(v_x_2104_);
    lean_dec_ref(v_x_2102_);
    return v_res_2106_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1___redArg(
    mut v_x_2107_: *mut LeanObject,
    mut v_x_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2109_: u64 = 0;
    let mut v___x_2110_: usize = 0;
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2108_);
    v___x_2110_ = lean_uint64_to_usize(v___x_2109_);
    v___x_2111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2107_, v___x_2110_, v_x_2108_);
    return v___x_2111_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2112_: *mut LeanObject,
    mut v_x_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2114_: *mut LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1___redArg(v_x_2112_, v_x_2113_);
    lean_dec(v_x_2113_);
    lean_dec_ref(v_x_2112_);
    return v_res_2114_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(
    mut v_x_2115_: *mut LeanObject,
    mut v_x_2116_: *mut LeanObject,
    mut v_x_2117_: *mut LeanObject,
    mut v_x_2118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: u8 = 0;
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2119_ = lean_ctor_get(v_x_2115_, 0);
                v_vs_2120_ = lean_ctor_get(v_x_2115_, 1);
                v_isSharedCheck_2144_ = (!lean_is_exclusive(v_x_2115_)) as u8;
                if v_isSharedCheck_2144_ == 0 {
                    v___x_2122_ = v_x_2115_;
                    v_isShared_2123_ = v_isSharedCheck_2144_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2120_);
                    lean_inc(v_ks_2119_);
                    lean_dec(v_x_2115_);
                    v___x_2122_ = lean_box(0);
                    v_isShared_2123_ = v_isSharedCheck_2144_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2124_ = lean_array_get_size(v_ks_2119_);
                v___x_2125_ = lean_nat_dec_lt(v_x_2116_, v___x_2124_);
                if v___x_2125_ == 0 {
                    lean_dec(v_x_2116_);
                    v___x_2126_ = lean_array_push(v_ks_2119_, v_x_2117_);
                    v___x_2127_ = lean_array_push(v_vs_2120_, v_x_2118_);
                    if v_isShared_2123_ == 0 {
                        lean_ctor_set(v___x_2122_, 1, v___x_2127_);
                        lean_ctor_set(v___x_2122_, 0, v___x_2126_);
                        v___x_2129_ = v___x_2122_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2126_);
                        lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2127_);
                        v___x_2129_ = v_reuseFailAlloc_2130_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2131_ = lean_array_fget_borrowed(v_ks_2119_, v_x_2116_);
                    v___x_2132_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2117_, v_k_x27_2131_);
                    if v___x_2132_ == 0 {
                        if v_isShared_2123_ == 0 {
                            v___x_2134_ = v___x_2122_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_ks_2119_);
                            lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_vs_2120_);
                            v___x_2134_ = v_reuseFailAlloc_2138_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2139_ = lean_array_fset(v_ks_2119_, v_x_2116_, v_x_2117_);
                        v___x_2140_ = lean_array_fset(v_vs_2120_, v_x_2116_, v_x_2118_);
                        lean_dec(v_x_2116_);
                        if v_isShared_2123_ == 0 {
                            lean_ctor_set(v___x_2122_, 1, v___x_2140_);
                            lean_ctor_set(v___x_2122_, 0, v___x_2139_);
                            v___x_2142_ = v___x_2122_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2139_);
                            lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2140_);
                            v___x_2142_ = v_reuseFailAlloc_2143_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2129_;
            }
            3 => {
                v___x_2135_ = lean_unsigned_to_nat(1);
                v___x_2136_ = lean_nat_add(v_x_2116_, v___x_2135_);
                lean_dec(v_x_2116_);
                v_x_2115_ = v___x_2134_;
                v_x_2116_ = v___x_2136_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(
    mut v_n_2145_: *mut LeanObject,
    mut v_k_2146_: *mut LeanObject,
    mut v_v_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    v___x_2148_ = lean_unsigned_to_nat(0);
    v___x_2149_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(v_n_2145_, v___x_2148_, v_k_2146_, v_v_2147_);
    return v___x_2149_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    v___x_2150_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2150_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_x_2151_: *mut LeanObject,
    mut v_x_2152_: usize,
    mut v_x_2153_: usize,
    mut v_x_2154_: *mut LeanObject,
    mut v_x_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: usize = 0;
    let mut v___x_2158_: usize = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: usize = 0;
    let mut v_j_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2166_: u8 = 0;
    let mut v_v_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_node_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2191_: u8 = 0;
    let mut v___x_2192_: usize = 0;
    let mut v___x_2193_: usize = 0;
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v_unused_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2211_: u8 = 0;
    let mut v_ks_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: usize = 0;
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v_reuseFailAlloc_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2151_) == 0 {
                    v_es_2156_ = lean_ctor_get(v_x_2151_, 0);
                    v___x_2157_ = 5usize;
                    v___x_2158_ = 1usize;
                    v___x_2159_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
                    v___x_2160_ = lean_usize_land(v_x_2152_, v___x_2159_);
                    v_j_2161_ = lean_usize_to_nat(v___x_2160_);
                    v___x_2162_ = lean_array_get_size(v_es_2156_);
                    v___x_2163_ = lean_nat_dec_lt(v_j_2161_, v___x_2162_);
                    if v___x_2163_ == 0 {
                        lean_dec(v_j_2161_);
                        lean_dec(v_x_2155_);
                        lean_dec(v_x_2154_);
                        return v_x_2151_;
                    } else {
                        lean_inc_ref(v_es_2156_);
                        v_isSharedCheck_2200_ = (!lean_is_exclusive(v_x_2151_)) as u8;
                        if v_isSharedCheck_2200_ == 0 {
                            v_unused_2201_ = lean_ctor_get(v_x_2151_, 0);
                            lean_dec(v_unused_2201_);
                            v___x_2165_ = v_x_2151_;
                            v_isShared_2166_ = v_isSharedCheck_2200_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2151_);
                            v___x_2165_ = lean_box(0);
                            v_isShared_2166_ = v_isSharedCheck_2200_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2202_ = lean_ctor_get(v_x_2151_, 0);
                    v_vs_2203_ = lean_ctor_get(v_x_2151_, 1);
                    v_isSharedCheck_2223_ = (!lean_is_exclusive(v_x_2151_)) as u8;
                    if v_isSharedCheck_2223_ == 0 {
                        v___x_2205_ = v_x_2151_;
                        v_isShared_2206_ = v_isSharedCheck_2223_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2203_);
                        lean_inc(v_ks_2202_);
                        lean_dec(v_x_2151_);
                        v___x_2205_ = lean_box(0);
                        v_isShared_2206_ = v_isSharedCheck_2223_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2167_ = lean_array_fget(v_es_2156_, v_j_2161_);
                v___x_2168_ = lean_box(0);
                v_xs_x27_2169_ = lean_array_fset(v_es_2156_, v_j_2161_, v___x_2168_);
                match lean_obj_tag(v_v_2167_) {
                    0 => {
                        v_key_2176_ = lean_ctor_get(v_v_2167_, 0);
                        v_val_2177_ = lean_ctor_get(v_v_2167_, 1);
                        v_isSharedCheck_2187_ = (!lean_is_exclusive(v_v_2167_)) as u8;
                        if v_isSharedCheck_2187_ == 0 {
                            v___x_2179_ = v_v_2167_;
                            v_isShared_2180_ = v_isSharedCheck_2187_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2177_);
                            lean_inc(v_key_2176_);
                            lean_dec(v_v_2167_);
                            v___x_2179_ = lean_box(0);
                            v_isShared_2180_ = v_isSharedCheck_2187_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2188_ = lean_ctor_get(v_v_2167_, 0);
                        v_isSharedCheck_2198_ = (!lean_is_exclusive(v_v_2167_)) as u8;
                        if v_isSharedCheck_2198_ == 0 {
                            v___x_2190_ = v_v_2167_;
                            v_isShared_2191_ = v_isSharedCheck_2198_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2188_);
                            lean_dec(v_v_2167_);
                            v___x_2190_ = lean_box(0);
                            v_isShared_2191_ = v_isSharedCheck_2198_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2199_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2199_, 0, v_x_2154_);
                        lean_ctor_set(v___x_2199_, 1, v_x_2155_);
                        v___y_2171_ = v___x_2199_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2172_ = lean_array_fset(v_xs_x27_2169_, v_j_2161_, v___y_2171_);
                lean_dec(v_j_2161_);
                if v_isShared_2166_ == 0 {
                    lean_ctor_set(v___x_2165_, 0, v___x_2172_);
                    v___x_2174_ = v___x_2165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
                    v___x_2174_ = v_reuseFailAlloc_2175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2174_;
            }
            4 => {
                v___x_2181_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2154_, v_key_2176_);
                if v___x_2181_ == 0 {
                    lean_del_object(v___x_2179_);
                    v___x_2182_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2176_,
                        v_val_2177_,
                        v_x_2154_,
                        v_x_2155_,
                    );
                    v___x_2183_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2183_, 0, v___x_2182_);
                    v___y_2171_ = v___x_2183_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2177_);
                    lean_dec(v_key_2176_);
                    if v_isShared_2180_ == 0 {
                        lean_ctor_set(v___x_2179_, 1, v_x_2155_);
                        lean_ctor_set(v___x_2179_, 0, v_x_2154_);
                        v___x_2185_ = v___x_2179_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_x_2154_);
                        lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_x_2155_);
                        v___x_2185_ = v_reuseFailAlloc_2186_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2171_ = v___x_2185_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2192_ = lean_usize_shift_right(v_x_2152_, v___x_2157_);
                v___x_2193_ = lean_usize_add(v_x_2153_, v___x_2158_);
                v___x_2194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg(v_node_2188_, v___x_2192_, v___x_2193_, v_x_2154_, v_x_2155_);
                if v_isShared_2191_ == 0 {
                    lean_ctor_set(v___x_2190_, 0, v___x_2194_);
                    v___x_2196_ = v___x_2190_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
                    v___x_2196_ = v_reuseFailAlloc_2197_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2171_ = v___x_2196_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2206_ == 0 {
                    v___x_2208_ = v___x_2205_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_ks_2202_);
                    lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_vs_2203_);
                    v___x_2208_ = v_reuseFailAlloc_2222_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2209_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___x_2208_, v_x_2154_, v_x_2155_);
                v___x_2217_ = 7usize;
                v___x_2218_ = lean_usize_dec_le(v___x_2217_, v_x_2153_);
                if v___x_2218_ == 0 {
                    v___x_2219_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2209_);
                    v___x_2220_ = lean_unsigned_to_nat(4);
                    v___x_2221_ = lean_nat_dec_lt(v___x_2219_, v___x_2220_);
                    lean_dec(v___x_2219_);
                    v___y_2211_ = v___x_2221_;
                    state = 10;
                    continue;
                } else {
                    v___y_2211_ = v___x_2218_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2211_ == 0 {
                    v_ks_2212_ = lean_ctor_get(v_newNode_2209_, 0);
                    lean_inc_ref(v_ks_2212_);
                    v_vs_2213_ = lean_ctor_get(v_newNode_2209_, 1);
                    lean_inc_ref(v_vs_2213_);
                    lean_dec_ref(v_newNode_2209_);
                    v___x_2214_ = lean_unsigned_to_nat(0);
                    v___x_2215_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg___closed__0);
                    v___x_2216_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_x_2153_, v_ks_2212_, v_vs_2213_, v___x_2214_, v___x_2215_);
                    lean_dec_ref(v_vs_2213_);
                    lean_dec_ref(v_ks_2212_);
                    return v___x_2216_;
                } else {
                    return v_newNode_2209_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(
    mut v_depth_2224_: usize,
    mut v_keys_2225_: *mut LeanObject,
    mut v_vals_2226_: *mut LeanObject,
    mut v_i_2227_: *mut LeanObject,
    mut v_entries_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: u8 = 0;
    let mut v_k_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: u64 = 0;
    let mut v_h_2234_: usize = 0;
    let mut v___x_2235_: usize = 0;
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: usize = 0;
    let mut v___x_2239_: usize = 0;
    let mut v_h_2240_: usize = 0;
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2229_ = lean_array_get_size(v_keys_2225_);
                v___x_2230_ = lean_nat_dec_lt(v_i_2227_, v___x_2229_);
                if v___x_2230_ == 0 {
                    lean_dec(v_i_2227_);
                    return v_entries_2228_;
                } else {
                    v_k_2231_ = lean_array_fget_borrowed(v_keys_2225_, v_i_2227_);
                    v_v_2232_ = lean_array_fget_borrowed(v_vals_2226_, v_i_2227_);
                    v___x_2233_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_2231_);
                    v_h_2234_ = lean_uint64_to_usize(v___x_2233_);
                    v___x_2235_ = 5usize;
                    v___x_2236_ = lean_unsigned_to_nat(1);
                    v___x_2237_ = 1usize;
                    v___x_2238_ = lean_usize_sub(v_depth_2224_, v___x_2237_);
                    v___x_2239_ = lean_usize_mul(v___x_2235_, v___x_2238_);
                    v_h_2240_ = lean_usize_shift_right(v_h_2234_, v___x_2239_);
                    v___x_2241_ = lean_nat_add(v_i_2227_, v___x_2236_);
                    lean_dec(v_i_2227_);
                    lean_inc(v_v_2232_);
                    lean_inc(v_k_2231_);
                    v___x_2242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg(v_entries_2228_, v_h_2240_, v_depth_2224_, v_k_2231_, v_v_2232_);
                    v_i_2227_ = v___x_2241_;
                    v_entries_2228_ = v___x_2242_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_2244_: *mut LeanObject,
    mut v_keys_2245_: *mut LeanObject,
    mut v_vals_2246_: *mut LeanObject,
    mut v_i_2247_: *mut LeanObject,
    mut v_entries_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2249_: usize = 0;
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2249_ = lean_unbox_usize(v_depth_2244_);
    lean_dec(v_depth_2244_);
    v_res_2250_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_depth_boxed_2249_, v_keys_2245_, v_vals_2246_, v_i_2247_, v_entries_2248_);
    lean_dec_ref(v_vals_2246_);
    lean_dec_ref(v_keys_2245_);
    return v_res_2250_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_x_2251_: *mut LeanObject,
    mut v_x_2252_: *mut LeanObject,
    mut v_x_2253_: *mut LeanObject,
    mut v_x_2254_: *mut LeanObject,
    mut v_x_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1703__boxed_2256_: usize = 0;
    let mut v_x_1704__boxed_2257_: usize = 0;
    let mut v_res_2258_: *mut LeanObject = core::ptr::null_mut();
    v_x_1703__boxed_2256_ = lean_unbox_usize(v_x_2252_);
    lean_dec(v_x_2252_);
    v_x_1704__boxed_2257_ = lean_unbox_usize(v_x_2253_);
    lean_dec(v_x_2253_);
    v_res_2258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2251_, v_x_1703__boxed_2256_, v_x_1704__boxed_2257_, v_x_2254_, v_x_2255_);
    return v_res_2258_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2___redArg(
    mut v_x_2259_: *mut LeanObject,
    mut v_x_2260_: *mut LeanObject,
    mut v_x_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2262_: u64 = 0;
    let mut v___x_2263_: usize = 0;
    let mut v___x_2264_: usize = 0;
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    v___x_2262_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2260_);
    v___x_2263_ = lean_uint64_to_usize(v___x_2262_);
    v___x_2264_ = 1usize;
    v___x_2265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2259_, v___x_2263_, v___x_2264_, v_x_2260_, v_x_2261_);
    return v___x_2265_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(
    mut v_a_2266_: *mut LeanObject,
    mut v_b_2267_: *mut LeanObject,
) -> u8 {
    let mut v_fst_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    v_fst_2268_ = lean_ctor_get(v_a_2266_, 0);
    v_fst_2269_ = lean_ctor_get(v_b_2267_, 0);
    v___x_2270_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_2268_, v_fst_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1___boxed(
    mut v_a_2271_: *mut LeanObject,
    mut v_b_2272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2273_: u8 = 0;
    let mut v_r_2274_: *mut LeanObject = core::ptr::null_mut();
    v_res_2273_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(v_a_2271_, v_b_2272_);
    lean_dec_ref(v_b_2272_);
    lean_dec_ref(v_a_2271_);
    v_r_2274_ = lean_box((v_res_2273_) as usize);
    return v_r_2274_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__0(
    mut v_x_2275_: *mut LeanObject,
    mut v_keys_2276_: *mut LeanObject,
    mut v_v_2277_: *mut LeanObject,
    mut v_k_2278_: *mut LeanObject,
    mut v_x_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    v___x_2280_ = lean_unsigned_to_nat(1);
    v___x_2281_ = lean_nat_add(v_x_2275_, v___x_2280_);
    v_c_2282_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        lean_box(0),
        v_keys_2276_,
        v_v_2277_,
        v___x_2281_,
    );
    lean_dec(v___x_2281_);
    v___x_2283_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2283_, 0, v_k_2278_);
    lean_ctor_set(v___x_2283_, 1, v_c_2282_);
    return v___x_2283_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__0___boxed(
    mut v_x_2284_: *mut LeanObject,
    mut v_keys_2285_: *mut LeanObject,
    mut v_v_2286_: *mut LeanObject,
    mut v_k_2287_: *mut LeanObject,
    mut v_x_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2289_: *mut LeanObject = core::ptr::null_mut();
    v_res_2289_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_2284_, v_keys_2285_, v_v_2286_, v_k_2287_, v_x_2288_);
    lean_dec_ref(v_keys_2285_);
    lean_dec(v_x_2284_);
    return v_res_2289_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__6_spec__11(
    mut v_vs_2290_: *mut LeanObject,
    mut v_v_2291_: *mut LeanObject,
    mut v_i_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2293_ = lean_array_get_size(v_vs_2290_);
                v___x_2294_ = lean_nat_dec_lt(v_i_2292_, v___x_2293_);
                if v___x_2294_ == 0 {
                    lean_dec(v_i_2292_);
                    v___x_2295_ = lean_array_push(v_vs_2290_, v_v_2291_);
                    return v___x_2295_;
                } else {
                    v_expr_2296_ = lean_ctor_get(v_v_2291_, 0);
                    v___x_2297_ = lean_array_fget_borrowed(v_vs_2290_, v_i_2292_);
                    v_expr_2298_ = lean_ctor_get(v___x_2297_, 0);
                    v___x_2299_ = lean_expr_eqv(v_expr_2296_, v_expr_2298_);
                    if v___x_2299_ == 0 {
                        v___x_2300_ = lean_unsigned_to_nat(1);
                        v___x_2301_ = lean_nat_add(v_i_2292_, v___x_2300_);
                        lean_dec(v_i_2292_);
                        v_i_2292_ = v___x_2301_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2303_ = lean_array_fset(v_vs_2290_, v_i_2292_, v_v_2291_);
                        lean_dec(v_i_2292_);
                        return v___x_2303_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__6(
    mut v_vs_2304_: *mut LeanObject,
    mut v_v_2305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    v___x_2306_ = lean_unsigned_to_nat(0);
    v___x_2307_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__6_spec__11(v_vs_2304_, v_v_2305_, v___x_2306_);
    return v___x_2307_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(
    mut v_x_2312_: *mut LeanObject,
    mut v_keys_2313_: *mut LeanObject,
    mut v_v_2314_: *mut LeanObject,
    mut v_k_2315_: *mut LeanObject,
    mut v_as_2316_: *mut LeanObject,
    mut v_k_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
    mut v_x_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_midVal_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: u8 = 0;
    let mut v_snd_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2340_: u8 = 0;
    let mut v_unused_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2320_ = lean_nat_add(v_x_2318_, v_x_2319_);
                v___x_2321_ = lean_unsigned_to_nat(1);
                v_mid_2322_ = lean_nat_shiftr(v___x_2320_, v___x_2321_);
                lean_dec(v___x_2320_);
                v_midVal_2323_ = lean_array_fget(v_as_2316_, v_mid_2322_);
                v___x_2324_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(v_midVal_2323_, v_k_2317_);
                if v___x_2324_ == 0 {
                    lean_dec(v_x_2319_);
                    v___x_2325_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(v_k_2317_, v_midVal_2323_);
                    if v___x_2325_ == 0 {
                        lean_dec(v_x_2318_);
                        v___x_2326_ = lean_array_get_size(v_as_2316_);
                        v___x_2327_ = lean_nat_dec_lt(v_mid_2322_, v___x_2326_);
                        if v___x_2327_ == 0 {
                            lean_dec(v_midVal_2323_);
                            lean_dec(v_mid_2322_);
                            lean_dec(v_k_2315_);
                            lean_dec_ref(v_v_2314_);
                            return v_as_2316_;
                        } else {
                            v_snd_2328_ = lean_ctor_get(v_midVal_2323_, 1);
                            v_isSharedCheck_2340_ = (!lean_is_exclusive(v_midVal_2323_)) as u8;
                            if v_isSharedCheck_2340_ == 0 {
                                v_unused_2341_ = lean_ctor_get(v_midVal_2323_, 0);
                                lean_dec(v_unused_2341_);
                                v___x_2330_ = v_midVal_2323_;
                                v_isShared_2331_ = v_isSharedCheck_2340_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_2328_);
                                lean_dec(v_midVal_2323_);
                                v___x_2330_ = lean_box(0);
                                v_isShared_2331_ = v_isSharedCheck_2340_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_midVal_2323_);
                        v_x_2319_ = v_mid_2322_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_midVal_2323_);
                    v___x_2343_ = lean_nat_dec_eq(v_mid_2322_, v_x_2318_);
                    if v___x_2343_ == 0 {
                        lean_dec(v_x_2318_);
                        v_x_2318_ = v_mid_2322_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_mid_2322_);
                        lean_dec(v_x_2319_);
                        v___x_2345_ = lean_nat_add(v_x_2312_, v___x_2321_);
                        v_c_2346_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_2313_, v_v_2314_, v___x_2345_);
                        lean_dec(v___x_2345_);
                        v___x_2347_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2347_, 0, v_k_2315_);
                        lean_ctor_set(v___x_2347_, 1, v_c_2346_);
                        v___x_2348_ = lean_nat_add(v_x_2318_, v___x_2321_);
                        lean_dec(v_x_2318_);
                        v_j_2349_ = lean_array_get_size(v_as_2316_);
                        v_as_2350_ = lean_array_push(v_as_2316_, v___x_2347_);
                        v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            lean_box(0),
                            v___x_2348_,
                            v_as_2350_,
                            v_j_2349_,
                        );
                        lean_dec(v___x_2348_);
                        return v___x_2351_;
                    }
                }
            }
            1 => {
                v___x_2332_ = lean_box(0);
                v_xs_x27_2333_ = lean_array_fset(v_as_2316_, v_mid_2322_, v___x_2332_);
                v___x_2334_ = lean_nat_add(v_x_2312_, v___x_2321_);
                v_c_2335_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3(v_keys_2313_, v_v_2314_, v___x_2334_, v_snd_2328_);
                lean_dec(v___x_2334_);
                if v_isShared_2331_ == 0 {
                    lean_ctor_set(v___x_2330_, 1, v_c_2335_);
                    lean_ctor_set(v___x_2330_, 0, v_k_2315_);
                    v___x_2337_ = v___x_2330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_k_2315_);
                    lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_c_2335_);
                    v___x_2337_ = v_reuseFailAlloc_2339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2338_ = lean_array_fset(v_xs_x27_2333_, v_mid_2322_, v___x_2337_);
                lean_dec(v_mid_2322_);
                return v___x_2338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7(
    mut v_x_2352_: *mut LeanObject,
    mut v_keys_2353_: *mut LeanObject,
    mut v_v_2354_: *mut LeanObject,
    mut v_k_2355_: *mut LeanObject,
    mut v_as_2356_: *mut LeanObject,
    mut v_k_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    v___x_2358_ = lean_array_get_size(v_as_2356_);
    v___x_2359_ = lean_unsigned_to_nat(0);
    v___x_2360_ = lean_nat_dec_eq(v___x_2358_, v___x_2359_);
    if v___x_2360_ == 0 {
        let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: u8 = 0;
        v___x_2361_ = lean_array_fget_borrowed(v_as_2356_, v___x_2359_);
        v___x_2362_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(v_k_2357_, v___x_2361_);
        if v___x_2362_ == 0 {
            let mut v___x_2363_: u8 = 0;
            v___x_2363_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(v___x_2361_, v_k_2357_);
            if v___x_2363_ == 0 {
                let mut v___x_2364_: u8 = 0;
                v___x_2364_ = lean_nat_dec_lt(v___x_2359_, v___x_2358_);
                if v___x_2364_ == 0 {
                    lean_dec(v_k_2355_);
                    lean_dec_ref(v_v_2354_);
                    return v_as_2356_;
                } else {
                    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_2366_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc(v___x_2361_);
                    v___x_2365_ = lean_box(0);
                    v_xs_x27_2366_ = lean_array_fset(v_as_2356_, v___x_2359_, v___x_2365_);
                    v___x_2367_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_2352_, v_keys_2353_, v_v_2354_, v_k_2355_, v___x_2361_);
                    v___x_2368_ = lean_array_fset(v_xs_x27_2366_, v___x_2359_, v___x_2367_);
                    return v___x_2368_;
                }
            } else {
                let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2372_: u8 = 0;
                v___x_2369_ = lean_unsigned_to_nat(1);
                v___x_2370_ = lean_nat_sub(v___x_2358_, v___x_2369_);
                v___x_2371_ = lean_array_fget_borrowed(v_as_2356_, v___x_2370_);
                v___x_2372_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(v___x_2371_, v_k_2357_);
                if v___x_2372_ == 0 {
                    let mut v___x_2373_: u8 = 0;
                    v___x_2373_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__1(v_k_2357_, v___x_2371_);
                    if v___x_2373_ == 0 {
                        let mut v___x_2374_: u8 = 0;
                        v___x_2374_ = lean_nat_dec_lt(v___x_2370_, v___x_2358_);
                        if v___x_2374_ == 0 {
                            lean_dec(v___x_2370_);
                            lean_dec(v_k_2355_);
                            lean_dec_ref(v_v_2354_);
                            return v_as_2356_;
                        } else {
                            let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_xs_x27_2376_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
                            lean_inc(v___x_2371_);
                            v___x_2375_ = lean_box(0);
                            v_xs_x27_2376_ = lean_array_fset(v_as_2356_, v___x_2370_, v___x_2375_);
                            v___x_2377_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_2352_, v_keys_2353_, v_v_2354_, v_k_2355_, v___x_2371_);
                            v___x_2378_ = lean_array_fset(v_xs_x27_2376_, v___x_2370_, v___x_2377_);
                            lean_dec(v___x_2370_);
                            return v___x_2378_;
                        }
                    } else {
                        let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2379_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_2352_, v_keys_2353_, v_v_2354_, v_k_2355_, v_as_2356_, v_k_2357_, v___x_2359_, v___x_2370_);
                        return v___x_2379_;
                    }
                } else {
                    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_2370_);
                    v___x_2380_ = lean_box(0);
                    v___x_2381_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_2352_, v_keys_2353_, v_v_2354_, v_k_2355_, v___x_2380_);
                    v___x_2382_ = lean_array_push(v_as_2356_, v___x_2381_);
                    return v___x_2382_;
                }
            }
        } else {
            let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
            let mut v_as_2385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
            v___x_2383_ = lean_box(0);
            v___x_2384_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_2352_, v_keys_2353_, v_v_2354_, v_k_2355_, v___x_2383_);
            v_as_2385_ = lean_array_push(v_as_2356_, v___x_2384_);
            v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                lean_box(0),
                v___x_2359_,
                v_as_2385_,
                v___x_2358_,
            );
            return v___x_2386_;
        }
    } else {
        let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
        v___x_2387_ = lean_box(0);
        v___x_2388_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_2352_, v_keys_2353_, v_v_2354_, v_k_2355_, v___x_2387_);
        v___x_2389_ = lean_array_push(v_as_2356_, v___x_2388_);
        return v___x_2389_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3(
    mut v_keys_2390_: *mut LeanObject,
    mut v_v_2391_: *mut LeanObject,
    mut v_x_2392_: *mut LeanObject,
    mut v_x_2393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_2394_ = lean_ctor_get(v_x_2393_, 0);
                v_children_2395_ = lean_ctor_get(v_x_2393_, 1);
                v_isSharedCheck_2412_ = (!lean_is_exclusive(v_x_2393_)) as u8;
                if v_isSharedCheck_2412_ == 0 {
                    v___x_2397_ = v_x_2393_;
                    v_isShared_2398_ = v_isSharedCheck_2412_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_children_2395_);
                    lean_inc(v_vs_2394_);
                    lean_dec(v_x_2393_);
                    v___x_2397_ = lean_box(0);
                    v_isShared_2398_ = v_isSharedCheck_2412_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2399_ = lean_array_get_size(v_keys_2390_);
                v___x_2400_ = lean_nat_dec_lt(v_x_2392_, v___x_2399_);
                if v___x_2400_ == 0 {
                    v___x_2401_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__6(v_vs_2394_, v_v_2391_);
                    if v_isShared_2398_ == 0 {
                        lean_ctor_set(v___x_2397_, 0, v___x_2401_);
                        v___x_2403_ = v___x_2397_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
                        lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_children_2395_);
                        v___x_2403_ = v_reuseFailAlloc_2404_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_2405_ = lean_array_fget_borrowed(v_keys_2390_, v_x_2392_);
                    v___x_2406_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___closed__1;
                    lean_inc_n(v_k_2405_, 2);
                    v___x_2407_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2407_, 0, v_k_2405_);
                    lean_ctor_set(v___x_2407_, 1, v___x_2406_);
                    v_c_2408_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7(v_x_2392_, v_keys_2390_, v_v_2391_, v_k_2405_, v_children_2395_, v___x_2407_);
                    lean_dec_ref_known(v___x_2407_, 2);
                    if v_isShared_2398_ == 0 {
                        lean_ctor_set(v___x_2397_, 1, v_c_2408_);
                        v___x_2410_ = v___x_2397_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_vs_2394_);
                        lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_c_2408_);
                        v___x_2410_ = v_reuseFailAlloc_2411_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2403_;
            }
            3 => {
                return v___x_2410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__2(
    mut v_x_2413_: *mut LeanObject,
    mut v_keys_2414_: *mut LeanObject,
    mut v_v_2415_: *mut LeanObject,
    mut v_k_2416_: *mut LeanObject,
    mut v_x_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut v_unused_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2418_ = lean_ctor_get(v_x_2417_, 1);
                v_isSharedCheck_2428_ = (!lean_is_exclusive(v_x_2417_)) as u8;
                if v_isSharedCheck_2428_ == 0 {
                    v_unused_2429_ = lean_ctor_get(v_x_2417_, 0);
                    lean_dec(v_unused_2429_);
                    v___x_2420_ = v_x_2417_;
                    v_isShared_2421_ = v_isSharedCheck_2428_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2418_);
                    lean_dec(v_x_2417_);
                    v___x_2420_ = lean_box(0);
                    v_isShared_2421_ = v_isSharedCheck_2428_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2422_ = lean_unsigned_to_nat(1);
                v___x_2423_ = lean_nat_add(v_x_2413_, v___x_2422_);
                v_c_2424_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3(v_keys_2414_, v_v_2415_, v___x_2423_, v_snd_2418_);
                lean_dec(v___x_2423_);
                if v_isShared_2421_ == 0 {
                    lean_ctor_set(v___x_2420_, 1, v_c_2424_);
                    lean_ctor_set(v___x_2420_, 0, v_k_2416_);
                    v___x_2426_ = v___x_2420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_k_2416_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_c_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__2___boxed(
    mut v_x_2430_: *mut LeanObject,
    mut v_keys_2431_: *mut LeanObject,
    mut v_v_2432_: *mut LeanObject,
    mut v_k_2433_: *mut LeanObject,
    mut v_x_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2435_: *mut LeanObject = core::ptr::null_mut();
    v_res_2435_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_2430_, v_keys_2431_, v_v_2432_, v_k_2433_, v_x_2434_);
    lean_dec_ref(v_keys_2431_);
    lean_dec(v_x_2430_);
    return v_res_2435_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3___boxed(
    mut v_keys_2436_: *mut LeanObject,
    mut v_v_2437_: *mut LeanObject,
    mut v_x_2438_: *mut LeanObject,
    mut v_x_2439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2440_: *mut LeanObject = core::ptr::null_mut();
    v_res_2440_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3(v_keys_2436_, v_v_2437_, v_x_2438_, v_x_2439_);
    lean_dec(v_x_2438_);
    lean_dec_ref(v_keys_2436_);
    return v_res_2440_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13___redArg___boxed(
    mut v_x_2441_: *mut LeanObject,
    mut v_keys_2442_: *mut LeanObject,
    mut v_v_2443_: *mut LeanObject,
    mut v_k_2444_: *mut LeanObject,
    mut v_as_2445_: *mut LeanObject,
    mut v_k_2446_: *mut LeanObject,
    mut v_x_2447_: *mut LeanObject,
    mut v_x_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_2441_, v_keys_2442_, v_v_2443_, v_k_2444_, v_as_2445_, v_k_2446_, v_x_2447_, v_x_2448_);
    lean_dec_ref(v_k_2446_);
    lean_dec_ref(v_keys_2442_);
    lean_dec(v_x_2441_);
    return v_res_2449_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7___boxed(
    mut v_x_2450_: *mut LeanObject,
    mut v_keys_2451_: *mut LeanObject,
    mut v_v_2452_: *mut LeanObject,
    mut v_k_2453_: *mut LeanObject,
    mut v_as_2454_: *mut LeanObject,
    mut v_k_2455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2456_: *mut LeanObject = core::ptr::null_mut();
    v_res_2456_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7(v_x_2450_, v_keys_2451_, v_v_2452_, v_k_2453_, v_as_2454_, v_k_2455_);
    lean_dec_ref(v_k_2455_);
    lean_dec_ref(v_keys_2451_);
    lean_dec(v_x_2450_);
    return v_res_2456_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
    return v___x_2457_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4(
    mut v_msg_2458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2459_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4___closed__0);
    v___x_2460_ = lean_panic_fn_borrowed(v___x_2459_, v_msg_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2464_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__2;
    v___x_2465_ = lean_unsigned_to_nat(23);
    v___x_2466_ = lean_unsigned_to_nat(166);
    v___x_2467_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__1;
    v___x_2468_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__0;
    v___x_2469_ = l_mkPanicMessageWithDecl(
        v___x_2468_,
        v___x_2467_,
        v___x_2466_,
        v___x_2465_,
        v___x_2464_,
    );
    return v___x_2469_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0(
    mut v_d_2470_: *mut LeanObject,
    mut v_keys_2471_: *mut LeanObject,
    mut v_v_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: u8 = 0;
    v___x_2473_ = lean_array_get_size(v_keys_2471_);
    v___x_2474_ = lean_unsigned_to_nat(0);
    v___x_2475_ = lean_nat_dec_eq(v___x_2473_, v___x_2474_);
    if v___x_2475_ == 0 {
        let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_2477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
        v___x_2476_ = lean_box(0);
        v_k_2477_ = lean_array_get_borrowed(v___x_2476_, v_keys_2471_, v___x_2474_);
        v___x_2478_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1___redArg(v_d_2470_, v_k_2477_);
        if lean_obj_tag(v___x_2478_) == 0 {
            let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_2480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
            v___x_2479_ = lean_unsigned_to_nat(1);
            v_c_2480_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                lean_box(0),
                v_keys_2471_,
                v_v_2472_,
                v___x_2479_,
            );
            lean_inc(v_k_2477_);
            v___x_2481_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2___redArg(v_d_2470_, v_k_2477_, v_c_2480_);
            return v___x_2481_;
        } else {
            let mut v_val_2482_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_2484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
            v_val_2482_ = lean_ctor_get(v___x_2478_, 0);
            lean_inc(v_val_2482_);
            lean_dec_ref_known(v___x_2478_, 1);
            v___x_2483_ = lean_unsigned_to_nat(1);
            v_c_2484_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3(v_keys_2471_, v_v_2472_, v___x_2483_, v_val_2482_);
            lean_inc(v_k_2477_);
            v___x_2485_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2___redArg(v_d_2470_, v_k_2477_, v_c_2484_);
            return v___x_2485_;
        }
    } else {
        let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_v_2472_);
        lean_dec_ref(v_d_2470_);
        v___x_2486_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___closed__3);
        v___x_2487_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__4(v___x_2486_);
        return v___x_2487_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0___boxed(
    mut v_d_2488_: *mut LeanObject,
    mut v_keys_2489_: *mut LeanObject,
    mut v_v_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2491_: *mut LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0(v_d_2488_, v_keys_2489_, v_v_2490_);
    lean_dec_ref(v_keys_2489_);
    return v_res_2491_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0(
    mut v_d_2492_: *mut LeanObject,
    mut v_p_2493_: *mut LeanObject,
    mut v_v_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keys_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    v_keys_2495_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_2493_);
    v___x_2496_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0(v_d_2492_, v_keys_2495_, v_v_2494_);
    lean_dec_ref(v_keys_2495_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_insert(
    mut v_thms_2497_: *mut LeanObject,
    mut v_thm_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pattern_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v_pattern_2499_ = lean_ctor_get(v_thm_2498_, 1);
    lean_inc_ref(v_pattern_2499_);
    v___x_2500_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0(
        v_thms_2497_,
        v_pattern_2499_,
        v_thm_2498_,
    );
    return v___x_2500_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2501_: *mut LeanObject,
    mut v_x_2502_: *mut LeanObject,
    mut v_x_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    v___x_2504_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1___redArg(v_x_2502_, v_x_2503_);
    return v___x_2504_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2505_: *mut LeanObject,
    mut v_x_2506_: *mut LeanObject,
    mut v_x_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2508_: *mut LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1(v_00_u03b2_2505_, v_x_2506_, v_x_2507_);
    lean_dec(v_x_2507_);
    lean_dec_ref(v_x_2506_);
    return v_res_2508_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2509_: *mut LeanObject,
    mut v_x_2510_: *mut LeanObject,
    mut v_x_2511_: *mut LeanObject,
    mut v_x_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2___redArg(v_x_2510_, v_x_2511_, v_x_2512_);
    return v___x_2513_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2514_: *mut LeanObject,
    mut v_x_2515_: *mut LeanObject,
    mut v_x_2516_: usize,
    mut v_x_2517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2515_, v_x_2516_, v_x_2517_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_2519_: *mut LeanObject,
    mut v_x_2520_: *mut LeanObject,
    mut v_x_2521_: *mut LeanObject,
    mut v_x_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2191__boxed_2523_: usize = 0;
    let mut v_res_2524_: *mut LeanObject = core::ptr::null_mut();
    v_x_2191__boxed_2523_ = lean_unbox_usize(v_x_2521_);
    lean_dec(v_x_2521_);
    v_res_2524_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2519_, v_x_2520_, v_x_2191__boxed_2523_, v_x_2522_);
    lean_dec(v_x_2522_);
    lean_dec_ref(v_x_2520_);
    return v_res_2524_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_2525_: *mut LeanObject,
    mut v_x_2526_: *mut LeanObject,
    mut v_x_2527_: usize,
    mut v_x_2528_: usize,
    mut v_x_2529_: *mut LeanObject,
    mut v_x_2530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    v___x_2531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2526_, v_x_2527_, v_x_2528_, v_x_2529_, v_x_2530_);
    return v___x_2531_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_2532_: *mut LeanObject,
    mut v_x_2533_: *mut LeanObject,
    mut v_x_2534_: *mut LeanObject,
    mut v_x_2535_: *mut LeanObject,
    mut v_x_2536_: *mut LeanObject,
    mut v_x_2537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2202__boxed_2538_: usize = 0;
    let mut v_x_2203__boxed_2539_: usize = 0;
    let mut v_res_2540_: *mut LeanObject = core::ptr::null_mut();
    v_x_2202__boxed_2538_ = lean_unbox_usize(v_x_2534_);
    lean_dec(v_x_2534_);
    v_x_2203__boxed_2539_ = lean_unbox_usize(v_x_2535_);
    lean_dec(v_x_2535_);
    v_res_2540_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2532_, v_x_2533_, v_x_2202__boxed_2538_, v_x_2203__boxed_2539_, v_x_2536_, v_x_2537_);
    return v_res_2540_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2541_: *mut LeanObject,
    mut v_keys_2542_: *mut LeanObject,
    mut v_vals_2543_: *mut LeanObject,
    mut v_heq_2544_: *mut LeanObject,
    mut v_i_2545_: *mut LeanObject,
    mut v_k_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_keys_2542_, v_vals_2543_, v_i_2545_, v_k_2546_);
    return v___x_2547_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_2548_: *mut LeanObject,
    mut v_keys_2549_: *mut LeanObject,
    mut v_vals_2550_: *mut LeanObject,
    mut v_heq_2551_: *mut LeanObject,
    mut v_i_2552_: *mut LeanObject,
    mut v_k_2553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2554_: *mut LeanObject = core::ptr::null_mut();
    v_res_2554_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b2_2548_, v_keys_2549_, v_vals_2550_, v_heq_2551_, v_i_2552_, v_k_2553_);
    lean_dec(v_k_2553_);
    lean_dec_ref(v_vals_2550_);
    lean_dec_ref(v_keys_2549_);
    return v_res_2554_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7(
    mut v_00_u03b2_2555_: *mut LeanObject,
    mut v_n_2556_: *mut LeanObject,
    mut v_k_2557_: *mut LeanObject,
    mut v_v_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    v___x_2559_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_n_2556_, v_k_2557_, v_v_2558_);
    return v___x_2559_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8(
    mut v_00_u03b2_2560_: *mut LeanObject,
    mut v_depth_2561_: usize,
    mut v_keys_2562_: *mut LeanObject,
    mut v_vals_2563_: *mut LeanObject,
    mut v_heq_2564_: *mut LeanObject,
    mut v_i_2565_: *mut LeanObject,
    mut v_entries_2566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2567_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_depth_2561_, v_keys_2562_, v_vals_2563_, v_i_2565_, v_entries_2566_);
    return v___x_2567_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_2568_: *mut LeanObject,
    mut v_depth_2569_: *mut LeanObject,
    mut v_keys_2570_: *mut LeanObject,
    mut v_vals_2571_: *mut LeanObject,
    mut v_heq_2572_: *mut LeanObject,
    mut v_i_2573_: *mut LeanObject,
    mut v_entries_2574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2575_: usize = 0;
    let mut v_res_2576_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2575_ = lean_unbox_usize(v_depth_2569_);
    lean_dec(v_depth_2569_);
    v_res_2576_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__8(v_00_u03b2_2568_, v_depth_boxed_2575_, v_keys_2570_, v_vals_2571_, v_heq_2572_, v_i_2573_, v_entries_2574_);
    lean_dec_ref(v_vals_2571_);
    lean_dec_ref(v_keys_2570_);
    return v_res_2576_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13(
    mut v_x_2577_: *mut LeanObject,
    mut v_keys_2578_: *mut LeanObject,
    mut v_v_2579_: *mut LeanObject,
    mut v_k_2580_: *mut LeanObject,
    mut v_as_2581_: *mut LeanObject,
    mut v_k_2582_: *mut LeanObject,
    mut v_x_2583_: *mut LeanObject,
    mut v_x_2584_: *mut LeanObject,
    mut v_x_2585_: *mut LeanObject,
    mut v_x_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    v___x_2587_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_2577_, v_keys_2578_, v_v_2579_, v_k_2580_, v_as_2581_, v_k_2582_, v_x_2583_, v_x_2584_);
    return v___x_2587_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13___boxed(
    mut v_x_2588_: *mut LeanObject,
    mut v_keys_2589_: *mut LeanObject,
    mut v_v_2590_: *mut LeanObject,
    mut v_k_2591_: *mut LeanObject,
    mut v_as_2592_: *mut LeanObject,
    mut v_k_2593_: *mut LeanObject,
    mut v_x_2594_: *mut LeanObject,
    mut v_x_2595_: *mut LeanObject,
    mut v_x_2596_: *mut LeanObject,
    mut v_x_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2598_: *mut LeanObject = core::ptr::null_mut();
    v_res_2598_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__3_spec__7_spec__13(v_x_2588_, v_keys_2589_, v_v_2590_, v_k_2591_, v_as_2592_, v_k_2593_, v_x_2594_, v_x_2595_, v_x_2596_, v_x_2597_);
    lean_dec_ref(v_k_2593_);
    lean_dec_ref(v_keys_2589_);
    lean_dec(v_x_2588_);
    return v_res_2598_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9(
    mut v_00_u03b2_2599_: *mut LeanObject,
    mut v_x_2600_: *mut LeanObject,
    mut v_x_2601_: *mut LeanObject,
    mut v_x_2602_: *mut LeanObject,
    mut v_x_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2600_, v_x_2601_, v_x_2602_, v_x_2603_);
    return v___x_2604_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_getMatch(
    mut v_thms_2605_: *mut LeanObject,
    mut v_e_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    v___x_2607_ = l_Lean_Meta_Sym_getMatch___redArg(v_thms_2605_, v_e_2606_);
    return v___x_2607_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_getMatch___boxed(
    mut v_thms_2608_: *mut LeanObject,
    mut v_e_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2610_: *mut LeanObject = core::ptr::null_mut();
    v_res_2610_ = l_Lean_Meta_Sym_Simp_Theorems_getMatch(v_thms_2608_, v_e_2609_);
    lean_dec_ref(v_e_2609_);
    lean_dec_ref(v_thms_2608_);
    return v_res_2610_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(
    mut v_thms_2611_: *mut LeanObject,
    mut v_e_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2613_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_thms_2611_, v_e_2612_);
    return v___x_2613_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra___boxed(
    mut v_thms_2614_: *mut LeanObject,
    mut v_e_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2616_: *mut LeanObject = core::ptr::null_mut();
    v_res_2616_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_2614_, v_e_2615_);
    lean_dec_ref(v_e_2615_);
    lean_dec_ref(v_thms_2614_);
    return v_res_2616_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__0(
    mut v_x_2617_: *mut LeanObject,
    mut v_x_2618_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2617_) == 0 {
        if lean_obj_tag(v_x_2618_) == 0 {
            let mut v___x_2619_: u8 = 0;
            v___x_2619_ = 1;
            return v___x_2619_;
        } else {
            let mut v___x_2620_: u8 = 0;
            v___x_2620_ = 0;
            return v___x_2620_;
        }
    } else {
        if lean_obj_tag(v_x_2618_) == 0 {
            let mut v___x_2621_: u8 = 0;
            v___x_2621_ = 0;
            return v___x_2621_;
        } else {
            let mut v_val_2622_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2623_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2624_: u8 = 0;
            v_val_2622_ = lean_ctor_get(v_x_2617_, 0);
            v_val_2623_ = lean_ctor_get(v_x_2618_, 0);
            v___x_2624_ = lean_nat_dec_eq(v_val_2622_, v_val_2623_);
            return v___x_2624_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__0___boxed(
    mut v_x_2625_: *mut LeanObject,
    mut v_x_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2627_: u8 = 0;
    let mut v_r_2628_: *mut LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Option_instBEq_beq___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__0(v_x_2625_, v_x_2626_);
    lean_dec(v_x_2626_);
    lean_dec(v_x_2625_);
    v_r_2628_ = lean_box((v_res_2627_) as usize);
    return v_r_2628_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__1(
    mut v_a_2629_: *mut LeanObject,
    mut v_as_2630_: *mut LeanObject,
    mut v_i_2631_: usize,
    mut v_stop_2632_: usize,
) -> u8 {
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    let mut v___x_2636_: usize = 0;
    let mut v___x_2637_: usize = 0;
    let mut v___x_2639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2633_ = lean_usize_dec_eq(v_i_2631_, v_stop_2632_);
                if v___x_2633_ == 0 {
                    v___x_2634_ = lean_array_uget_borrowed(v_as_2630_, v_i_2631_);
                    v___x_2635_ = l_Option_instBEq_beq___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__0(v_a_2629_, v___x_2634_);
                    if v___x_2635_ == 0 {
                        v___x_2636_ = 1usize;
                        v___x_2637_ = lean_usize_add(v_i_2631_, v___x_2636_);
                        v_i_2631_ = v___x_2637_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2635_;
                    }
                } else {
                    v___x_2639_ = 0;
                    return v___x_2639_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__1___boxed(
    mut v_a_2640_: *mut LeanObject,
    mut v_as_2641_: *mut LeanObject,
    mut v_i_2642_: *mut LeanObject,
    mut v_stop_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2644_: usize = 0;
    let mut v_stop_boxed_2645_: usize = 0;
    let mut v_res_2646_: u8 = 0;
    let mut v_r_2647_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2644_ = lean_unbox_usize(v_i_2642_);
    lean_dec(v_i_2642_);
    v_stop_boxed_2645_ = lean_unbox_usize(v_stop_2643_);
    lean_dec(v_stop_2643_);
    v_res_2646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__1(v_a_2640_, v_as_2641_, v_i_boxed_2644_, v_stop_boxed_2645_);
    lean_dec_ref(v_as_2641_);
    lean_dec(v_a_2640_);
    v_r_2647_ = lean_box((v_res_2646_) as usize);
    return v_r_2647_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0(
    mut v_as_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
) -> u8 {
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: u8 = 0;
    v___x_2650_ = lean_unsigned_to_nat(0);
    v___x_2651_ = lean_array_get_size(v_as_2648_);
    v___x_2652_ = lean_nat_dec_lt(v___x_2650_, v___x_2651_);
    if v___x_2652_ == 0 {
        return v___x_2652_;
    } else {
        if v___x_2652_ == 0 {
            return v___x_2652_;
        } else {
            let mut v___x_2653_: usize = 0;
            let mut v___x_2654_: usize = 0;
            let mut v___x_2655_: u8 = 0;
            v___x_2653_ = 0usize;
            v___x_2654_ = lean_usize_of_nat(v___x_2651_);
            v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0_spec__1(v_a_2649_, v_as_2648_, v___x_2653_, v___x_2654_);
            return v___x_2655_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0___boxed(
    mut v_as_2656_: *mut LeanObject,
    mut v_a_2657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2658_: u8 = 0;
    let mut v_r_2659_: *mut LeanObject = core::ptr::null_mut();
    v_res_2658_ = l_Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0(v_as_2656_, v_a_2657_);
    lean_dec(v_a_2657_);
    lean_dec_ref(v_as_2656_);
    v_r_2659_ = lean_box((v_res_2658_) as usize);
    return v_r_2659_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux(
    mut v_a_2662_: *mut LeanObject,
    mut v_b_2663_: *mut LeanObject,
    mut v_a_2664_: *mut LeanObject,
    mut v_a_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_u2081_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_u2081_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_u2082_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_u2082_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2691_: u8 = 0;
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2708_: u8 = 0;
    let mut v___x_2709_: u8 = 0;
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2716_: u8 = 0;
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2719_: u8 = 0;
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2721_: u8 = 0;
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: u8 = 0;
    let mut v___x_2728_: u8 = 0;
    let mut v_expr_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_a_2662_) {
                    0 => match lean_obj_tag(v_b_2663_) {
                        0 => {
                            v_deBruijnIndex_2688_ = lean_ctor_get(v_a_2662_, 0);
                            v_deBruijnIndex_2689_ = lean_ctor_get(v_b_2663_, 0);
                            v___x_2727_ = lean_nat_dec_lt(v_deBruijnIndex_2688_, v_a_2664_);
                            if v___x_2727_ == 0 {
                                v___y_2719_ = v___x_2727_;
                                state = 6;
                                continue;
                            } else {
                                v___x_2728_ = lean_nat_dec_lt(v_deBruijnIndex_2689_, v_a_2664_);
                                v___y_2719_ = v___x_2728_;
                                state = 6;
                                continue;
                            }
                        }
                        10 => {
                            v_expr_2729_ = lean_ctor_get(v_b_2663_, 1);
                            v_b_2663_ = v_expr_2729_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec(v_a_2664_);
                            v_s_2667_ = v_a_2662_;
                            v_t_2668_ = v_b_2663_;
                            v___y_2669_ = v_a_2665_;
                            state = 1;
                            continue;
                        }
                    },
                    5 => match lean_obj_tag(v_b_2663_) {
                        5 => {
                            v_fn_2731_ = lean_ctor_get(v_a_2662_, 0);
                            v_arg_2732_ = lean_ctor_get(v_a_2662_, 1);
                            v_fn_2733_ = lean_ctor_get(v_b_2663_, 0);
                            v_arg_2734_ = lean_ctor_get(v_b_2663_, 1);
                            lean_inc(v_a_2664_);
                            v___x_2735_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux(v_fn_2731_, v_fn_2733_, v_a_2664_, v_a_2665_);
                            if lean_obj_tag(v___x_2735_) == 0 {
                                lean_dec(v_a_2664_);
                                return v___x_2735_;
                            } else {
                                v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
                                lean_inc(v_a_2736_);
                                lean_dec_ref_known(v___x_2735_, 1);
                                v_snd_2737_ = lean_ctor_get(v_a_2736_, 1);
                                lean_inc(v_snd_2737_);
                                lean_dec(v_a_2736_);
                                v_a_2662_ = v_arg_2732_;
                                v_b_2663_ = v_arg_2734_;
                                v_a_2665_ = v_snd_2737_;
                                state = 0;
                                continue;
                            }
                        }
                        10 => {
                            v_expr_2739_ = lean_ctor_get(v_b_2663_, 1);
                            v_b_2663_ = v_expr_2739_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec(v_a_2664_);
                            v_s_2667_ = v_a_2662_;
                            v_t_2668_ = v_b_2663_;
                            v___y_2669_ = v_a_2665_;
                            state = 1;
                            continue;
                        }
                    },
                    10 => {
                        v_expr_2741_ = lean_ctor_get(v_a_2662_, 1);
                        v_a_2662_ = v_expr_2741_;
                        state = 0;
                        continue;
                    }
                    7 => match lean_obj_tag(v_b_2663_) {
                        10 => {
                            v_expr_2743_ = lean_ctor_get(v_b_2663_, 1);
                            v_b_2663_ = v_expr_2743_;
                            state = 0;
                            continue;
                        }
                        7 => {
                            v_binderType_2745_ = lean_ctor_get(v_a_2662_, 1);
                            v_body_2746_ = lean_ctor_get(v_a_2662_, 2);
                            v_binderType_2747_ = lean_ctor_get(v_b_2663_, 1);
                            v_body_2748_ = lean_ctor_get(v_b_2663_, 2);
                            v_d_u2081_2676_ = v_binderType_2745_;
                            v_b_u2081_2677_ = v_body_2746_;
                            v_d_u2082_2678_ = v_binderType_2747_;
                            v_b_u2082_2679_ = v_body_2748_;
                            v___y_2680_ = v_a_2664_;
                            v___y_2681_ = v_a_2665_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            lean_dec(v_a_2664_);
                            v_s_2667_ = v_a_2662_;
                            v_t_2668_ = v_b_2663_;
                            v___y_2669_ = v_a_2665_;
                            state = 1;
                            continue;
                        }
                    },
                    6 => match lean_obj_tag(v_b_2663_) {
                        10 => {
                            v_expr_2749_ = lean_ctor_get(v_b_2663_, 1);
                            v_b_2663_ = v_expr_2749_;
                            state = 0;
                            continue;
                        }
                        6 => {
                            v_binderType_2751_ = lean_ctor_get(v_a_2662_, 1);
                            v_body_2752_ = lean_ctor_get(v_a_2662_, 2);
                            v_binderType_2753_ = lean_ctor_get(v_b_2663_, 1);
                            v_body_2754_ = lean_ctor_get(v_b_2663_, 2);
                            v_d_u2081_2676_ = v_binderType_2751_;
                            v_b_u2081_2677_ = v_body_2752_;
                            v_d_u2082_2678_ = v_binderType_2753_;
                            v_b_u2082_2679_ = v_body_2754_;
                            v___y_2680_ = v_a_2664_;
                            v___y_2681_ = v_a_2665_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            lean_dec(v_a_2664_);
                            v_s_2667_ = v_a_2662_;
                            v_t_2668_ = v_b_2663_;
                            v___y_2669_ = v_a_2665_;
                            state = 1;
                            continue;
                        }
                    },
                    _ => {
                        if lean_obj_tag(v_b_2663_) == 10 {
                            v_expr_2755_ = lean_ctor_get(v_b_2663_, 1);
                            v_b_2663_ = v_expr_2755_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_2664_);
                            v_s_2667_ = v_a_2662_;
                            v_t_2668_ = v_b_2663_;
                            v___y_2669_ = v_a_2665_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2670_ = lean_expr_eqv(v_s_2667_, v_t_2668_);
                if v___x_2670_ == 0 {
                    lean_dec_ref(v___y_2669_);
                    v___x_2671_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0;
                    return v___x_2671_;
                } else {
                    v___x_2672_ = lean_box(0);
                    v___x_2673_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2673_, 0, v___x_2672_);
                    lean_ctor_set(v___x_2673_, 1, v___y_2669_);
                    v___x_2674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2674_, 0, v___x_2673_);
                    return v___x_2674_;
                }
            }
            2 => {
                lean_inc(v___y_2680_);
                v___x_2682_ =
                    l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux(
                        v_d_u2081_2676_,
                        v_d_u2082_2678_,
                        v___y_2680_,
                        v___y_2681_,
                    );
                if lean_obj_tag(v___x_2682_) == 0 {
                    lean_dec(v___y_2680_);
                    return v___x_2682_;
                } else {
                    v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
                    lean_inc(v_a_2683_);
                    lean_dec_ref_known(v___x_2682_, 1);
                    v_snd_2684_ = lean_ctor_get(v_a_2683_, 1);
                    lean_inc(v_snd_2684_);
                    lean_dec(v_a_2683_);
                    v___x_2685_ = lean_unsigned_to_nat(1);
                    v___x_2686_ = lean_nat_add(v___y_2680_, v___x_2685_);
                    lean_dec(v___y_2680_);
                    v_a_2662_ = v_b_u2081_2677_;
                    v_b_2663_ = v_b_u2082_2679_;
                    v_a_2664_ = v___x_2686_;
                    v_a_2665_ = v_snd_2684_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                if v___y_2691_ == 0 {
                    lean_dec_ref(v_a_2665_);
                    lean_dec(v_a_2664_);
                    v___x_2692_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0;
                    return v___x_2692_;
                } else {
                    v___x_2693_ = lean_nat_sub(v_deBruijnIndex_2688_, v_a_2664_);
                    v___x_2694_ = lean_array_get_size(v_a_2665_);
                    v___x_2695_ = lean_nat_dec_le(v___x_2694_, v___x_2693_);
                    if v___x_2695_ == 0 {
                        v___x_2696_ = lean_nat_sub(v_deBruijnIndex_2689_, v_a_2664_);
                        lean_dec(v_a_2664_);
                        v___x_2697_ = lean_array_fget(v_a_2665_, v___x_2693_);
                        if lean_obj_tag(v___x_2697_) == 0 {
                            v___x_2698_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2698_, 0, v___x_2696_);
                            v___x_2699_ = l_Array_contains___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux_spec__0(v_a_2665_, v___x_2698_);
                            if v___x_2699_ == 0 {
                                v___x_2700_ = lean_array_fset(v_a_2665_, v___x_2693_, v___x_2698_);
                                lean_dec(v___x_2693_);
                                v___x_2701_ = lean_box(0);
                                v___x_2702_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_2702_, 0, v___x_2701_);
                                lean_ctor_set(v___x_2702_, 1, v___x_2700_);
                                v___x_2703_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2703_, 0, v___x_2702_);
                                return v___x_2703_;
                            } else {
                                lean_dec_ref_known(v___x_2698_, 1);
                                lean_dec(v___x_2693_);
                                lean_dec_ref(v_a_2665_);
                                v___x_2704_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0;
                                return v___x_2704_;
                            }
                        } else {
                            lean_dec(v___x_2693_);
                            v_val_2705_ = lean_ctor_get(v___x_2697_, 0);
                            v_isSharedCheck_2716_ = (!lean_is_exclusive(v___x_2697_)) as u8;
                            if v_isSharedCheck_2716_ == 0 {
                                v___x_2707_ = v___x_2697_;
                                v_isShared_2708_ = v_isSharedCheck_2716_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_val_2705_);
                                lean_dec(v___x_2697_);
                                v___x_2707_ = lean_box(0);
                                v_isShared_2708_ = v_isSharedCheck_2716_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2693_);
                        lean_dec_ref(v_a_2665_);
                        lean_dec(v_a_2664_);
                        v___x_2717_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0;
                        return v___x_2717_;
                    }
                }
            }
            4 => {
                v___x_2709_ = lean_nat_dec_eq(v___x_2696_, v_val_2705_);
                lean_dec(v_val_2705_);
                lean_dec(v___x_2696_);
                if v___x_2709_ == 0 {
                    lean_del_object(v___x_2707_);
                    lean_dec_ref(v_a_2665_);
                    v___x_2710_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0;
                    return v___x_2710_;
                } else {
                    v___x_2711_ = lean_box(0);
                    v___x_2712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2712_, 0, v___x_2711_);
                    lean_ctor_set(v___x_2712_, 1, v_a_2665_);
                    if v_isShared_2708_ == 0 {
                        lean_ctor_set(v___x_2707_, 0, v___x_2712_);
                        v___x_2714_ = v___x_2707_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
                        v___x_2714_ = v_reuseFailAlloc_2715_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2714_;
            }
            6 => {
                if v___y_2719_ == 0 {
                    v___x_2720_ = lean_nat_dec_le(v_a_2664_, v_deBruijnIndex_2688_);
                    if v___x_2720_ == 0 {
                        v___y_2691_ = v___x_2720_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2721_ = lean_nat_dec_le(v_a_2664_, v_deBruijnIndex_2689_);
                        v___y_2691_ = v___x_2721_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2664_);
                    v___x_2722_ = lean_nat_dec_eq(v_deBruijnIndex_2688_, v_deBruijnIndex_2689_);
                    if v___x_2722_ == 0 {
                        lean_dec_ref(v_a_2665_);
                        v___x_2723_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___closed__0;
                        return v___x_2723_;
                    } else {
                        v___x_2724_ = lean_box(0);
                        v___x_2725_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2725_, 0, v___x_2724_);
                        lean_ctor_set(v___x_2725_, 1, v_a_2665_);
                        v___x_2726_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2726_, 0, v___x_2725_);
                        return v___x_2726_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux___boxed(
    mut v_a_2757_: *mut LeanObject,
    mut v_b_2758_: *mut LeanObject,
    mut v_a_2759_: *mut LeanObject,
    mut v_a_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2761_: *mut LeanObject = core::ptr::null_mut();
    v_res_2761_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux(
        v_a_2757_, v_b_2758_, v_a_2759_, v_a_2760_,
    );
    lean_dec_ref(v_b_2758_);
    lean_dec_ref(v_a_2757_);
    return v_res_2761_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_isPerm(
    mut v_numVars_2762_: *mut LeanObject,
    mut v_lhs_2763_: *mut LeanObject,
    mut v_rhs_2764_: *mut LeanObject,
) -> u8 {
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    v___x_2765_ = lean_unsigned_to_nat(0);
    v___x_2766_ = lean_box(0);
    v___x_2767_ = lean_mk_array(v_numVars_2762_, v___x_2766_);
    v___x_2768_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_isPermAux(
        v_lhs_2763_,
        v_rhs_2764_,
        v___x_2765_,
        v___x_2767_,
    );
    if lean_obj_tag(v___x_2768_) == 1 {
        let mut v___x_2769_: u8 = 0;
        lean_dec_ref_known(v___x_2768_, 1);
        v___x_2769_ = 1;
        return v___x_2769_;
    } else {
        let mut v___x_2770_: u8 = 0;
        lean_dec_ref(v___x_2768_);
        v___x_2770_ = 0;
        return v___x_2770_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_isPerm___boxed(
    mut v_numVars_2771_: *mut LeanObject,
    mut v_lhs_2772_: *mut LeanObject,
    mut v_rhs_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2774_: u8 = 0;
    let mut v_r_2775_: *mut LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Lean_Meta_Sym_Simp_isPerm(v_numVars_2771_, v_lhs_2772_, v_rhs_2773_);
    lean_dec_ref(v_rhs_2773_);
    lean_dec_ref(v_lhs_2772_);
    v_r_2775_ = lean_box((v_res_2774_) as usize);
    return v_r_2775_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorIdx(
    mut v_x_2776_: u8,
) -> *mut LeanObject {
    match v_x_2776_ {
        0 => {
            let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
            v___x_2777_ = lean_unsigned_to_nat(0);
            return v___x_2777_;
        }
        1 => {
            let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
            v___x_2778_ = lean_unsigned_to_nat(1);
            return v___x_2778_;
        }
        2 => {
            let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
            v___x_2779_ = lean_unsigned_to_nat(2);
            return v___x_2779_;
        }
        _ => {
            let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
            v___x_2780_ = lean_unsigned_to_nat(3);
            return v___x_2780_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorIdx___boxed(
    mut v_x_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2782_: u8 = 0;
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2782_ = (lean_unbox(v_x_2781_) as u8);
    v_res_2783_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorIdx(
            v_x_boxed_2782_,
        );
    return v_res_2783_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_toCtorIdx(
    mut v_x_2784_: u8,
) -> *mut LeanObject {
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    v___x_2785_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorIdx(
            v_x_2784_,
        );
    return v___x_2785_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_toCtorIdx___boxed(
    mut v_x_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_2787_: u8 = 0;
    let mut v_res_2788_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2787_ = (lean_unbox(v_x_2786_) as u8);
    v_res_2788_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_toCtorIdx(
            v_x_4__boxed_2787_,
        );
    return v_res_2788_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorElim___redArg(
    mut v_k_2789_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2789_);
    return v_k_2789_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorElim___redArg___boxed(
    mut v_k_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2791_: *mut LeanObject = core::ptr::null_mut();
    v_res_2791_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorElim___redArg(v_k_2790_);
    lean_dec(v_k_2790_);
    return v_res_2791_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorElim(
    mut v_motive_2792_: *mut LeanObject,
    mut v_ctorIdx_2793_: *mut LeanObject,
    mut v_t_2794_: u8,
    mut v_h_2795_: *mut LeanObject,
    mut v_k_2796_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2796_);
    return v_k_2796_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorElim___boxed(
    mut v_motive_2797_: *mut LeanObject,
    mut v_ctorIdx_2798_: *mut LeanObject,
    mut v_t_2799_: *mut LeanObject,
    mut v_h_2800_: *mut LeanObject,
    mut v_k_2801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2802_: u8 = 0;
    let mut v_res_2803_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2802_ = (lean_unbox(v_t_2799_) as u8);
    v_res_2803_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_ctorElim(
            v_motive_2797_,
            v_ctorIdx_2798_,
            v_t_boxed_2802_,
            v_h_2800_,
            v_k_2801_,
        );
    lean_dec(v_k_2801_);
    lean_dec(v_ctorIdx_2798_);
    return v_res_2803_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eq_elim___redArg(
    mut v_eq_2804_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eq_2804_);
    return v_eq_2804_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eq_elim___redArg___boxed(
    mut v_eq_2805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2806_: *mut LeanObject = core::ptr::null_mut();
    v_res_2806_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eq_elim___redArg(
            v_eq_2805_,
        );
    lean_dec(v_eq_2805_);
    return v_res_2806_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eq_elim(
    mut v_motive_2807_: *mut LeanObject,
    mut v_t_2808_: u8,
    mut v_h_2809_: *mut LeanObject,
    mut v_eq_2810_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eq_2810_);
    return v_eq_2810_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eq_elim___boxed(
    mut v_motive_2811_: *mut LeanObject,
    mut v_t_2812_: *mut LeanObject,
    mut v_h_2813_: *mut LeanObject,
    mut v_eq_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2815_: u8 = 0;
    let mut v_res_2816_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2815_ = (lean_unbox(v_t_2812_) as u8);
    v_res_2816_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eq_elim(
            v_motive_2811_,
            v_t_boxed_2815_,
            v_h_2813_,
            v_eq_2814_,
        );
    lean_dec(v_eq_2814_);
    return v_res_2816_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqFalse_elim___redArg(
    mut v_eqFalse_2817_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eqFalse_2817_);
    return v_eqFalse_2817_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqFalse_elim___redArg___boxed(
    mut v_eqFalse_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2819_: *mut LeanObject = core::ptr::null_mut();
    v_res_2819_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqFalse_elim___redArg(v_eqFalse_2818_);
    lean_dec(v_eqFalse_2818_);
    return v_res_2819_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqFalse_elim(
    mut v_motive_2820_: *mut LeanObject,
    mut v_t_2821_: u8,
    mut v_h_2822_: *mut LeanObject,
    mut v_eqFalse_2823_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eqFalse_2823_);
    return v_eqFalse_2823_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqFalse_elim___boxed(
    mut v_motive_2824_: *mut LeanObject,
    mut v_t_2825_: *mut LeanObject,
    mut v_h_2826_: *mut LeanObject,
    mut v_eqFalse_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2828_: u8 = 0;
    let mut v_res_2829_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2828_ = (lean_unbox(v_t_2825_) as u8);
    v_res_2829_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqFalse_elim(
            v_motive_2824_,
            v_t_boxed_2828_,
            v_h_2826_,
            v_eqFalse_2827_,
        );
    lean_dec(v_eqFalse_2827_);
    return v_res_2829_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_iff_elim___redArg(
    mut v_iff_2830_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_iff_2830_);
    return v_iff_2830_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_iff_elim___redArg___boxed(
    mut v_iff_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2832_: *mut LeanObject = core::ptr::null_mut();
    v_res_2832_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_iff_elim___redArg(v_iff_2831_);
    lean_dec(v_iff_2831_);
    return v_res_2832_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_iff_elim(
    mut v_motive_2833_: *mut LeanObject,
    mut v_t_2834_: u8,
    mut v_h_2835_: *mut LeanObject,
    mut v_iff_2836_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_iff_2836_);
    return v_iff_2836_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_iff_elim___boxed(
    mut v_motive_2837_: *mut LeanObject,
    mut v_t_2838_: *mut LeanObject,
    mut v_h_2839_: *mut LeanObject,
    mut v_iff_2840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2841_: u8 = 0;
    let mut v_res_2842_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2841_ = (lean_unbox(v_t_2838_) as u8);
    v_res_2842_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_iff_elim(
            v_motive_2837_,
            v_t_boxed_2841_,
            v_h_2839_,
            v_iff_2840_,
        );
    lean_dec(v_iff_2840_);
    return v_res_2842_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqTrue_elim___redArg(
    mut v_eqTrue_2843_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eqTrue_2843_);
    return v_eqTrue_2843_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqTrue_elim___redArg___boxed(
    mut v_eqTrue_2844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2845_: *mut LeanObject = core::ptr::null_mut();
    v_res_2845_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqTrue_elim___redArg(v_eqTrue_2844_);
    lean_dec(v_eqTrue_2844_);
    return v_res_2845_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqTrue_elim(
    mut v_motive_2846_: *mut LeanObject,
    mut v_t_2847_: u8,
    mut v_h_2848_: *mut LeanObject,
    mut v_eqTrue_2849_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eqTrue_2849_);
    return v_eqTrue_2849_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqTrue_elim___boxed(
    mut v_motive_2850_: *mut LeanObject,
    mut v_t_2851_: *mut LeanObject,
    mut v_h_2852_: *mut LeanObject,
    mut v_eqTrue_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2854_: u8 = 0;
    let mut v_res_2855_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2854_ = (lean_unbox(v_t_2851_) as u8);
    v_res_2855_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_EqAdaptation_eqTrue_elim(
            v_motive_2850_,
            v_t_boxed_2854_,
            v_h_2852_,
            v_eqTrue_2853_,
        );
    lean_dec(v_eqTrue_2853_);
    return v_res_2855_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0_spec__0(
    mut v_msgData_2856_: *mut LeanObject,
    mut v___y_2857_: *mut LeanObject,
    mut v___y_2858_: *mut LeanObject,
    mut v___y_2859_: *mut LeanObject,
    mut v___y_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    v___x_2862_ = lean_st_ref_get(v___y_2860_);
    v_env_2863_ = lean_ctor_get(v___x_2862_, 0);
    lean_inc_ref(v_env_2863_);
    lean_dec(v___x_2862_);
    v___x_2864_ = lean_st_ref_get(v___y_2858_);
    v_mctx_2865_ = lean_ctor_get(v___x_2864_, 0);
    lean_inc_ref(v_mctx_2865_);
    lean_dec(v___x_2864_);
    v_lctx_2866_ = lean_ctor_get(v___y_2857_, 2);
    v_options_2867_ = lean_ctor_get(v___y_2859_, 2);
    lean_inc_ref(v_options_2867_);
    lean_inc_ref(v_lctx_2866_);
    v___x_2868_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2868_, 0, v_env_2863_);
    lean_ctor_set(v___x_2868_, 1, v_mctx_2865_);
    lean_ctor_set(v___x_2868_, 2, v_lctx_2866_);
    lean_ctor_set(v___x_2868_, 3, v_options_2867_);
    v___x_2869_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2869_, 0, v___x_2868_);
    lean_ctor_set(v___x_2869_, 1, v_msgData_2856_);
    v___x_2870_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    return v___x_2870_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0_spec__0___boxed(
    mut v_msgData_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
    mut v___y_2876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2877_: *mut LeanObject = core::ptr::null_mut();
    v_res_2877_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0_spec__0(v_msgData_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
    lean_dec(v___y_2875_);
    lean_dec_ref(v___y_2874_);
    lean_dec(v___y_2873_);
    lean_dec_ref(v___y_2872_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0___redArg(
    mut v_msg_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
    mut v___y_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
    mut v___y_2882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2884_ = lean_ctor_get(v___y_2881_, 5);
                v___x_2885_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0_spec__0(v_msg_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
                v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
                v_isSharedCheck_2894_ = (!lean_is_exclusive(v___x_2885_)) as u8;
                if v_isSharedCheck_2894_ == 0 {
                    v___x_2888_ = v___x_2885_;
                    v_isShared_2889_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2886_);
                    lean_dec(v___x_2885_);
                    v___x_2888_ = lean_box(0);
                    v_isShared_2889_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2884_);
                v___x_2890_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2890_, 0, v_ref_2884_);
                lean_ctor_set(v___x_2890_, 1, v_a_2886_);
                if v_isShared_2889_ == 0 {
                    lean_ctor_set_tag(v___x_2888_, 1);
                    lean_ctor_set(v___x_2888_, 0, v___x_2890_);
                    v___x_2892_ = v___x_2888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
                    v___x_2892_ = v_reuseFailAlloc_2893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0___redArg___boxed(
    mut v_msg_2895_: *mut LeanObject,
    mut v___y_2896_: *mut LeanObject,
    mut v___y_2897_: *mut LeanObject,
    mut v___y_2898_: *mut LeanObject,
    mut v___y_2899_: *mut LeanObject,
    mut v___y_2900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2901_: *mut LeanObject = core::ptr::null_mut();
    v_res_2901_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0___redArg(v_msg_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
    lean_dec(v___y_2899_);
    lean_dec_ref(v___y_2898_);
    lean_dec(v___y_2897_);
    lean_dec_ref(v___y_2896_);
    return v_res_2901_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__2()
-> *mut LeanObject {
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    v___x_2905_ = lean_box(0);
    v___x_2906_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__1;
    v___x_2907_ = l_Lean_mkConst(v___x_2906_, v___x_2905_);
    return v___x_2907_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__3()
-> *mut LeanObject {
    let mut v___x_2908_: u8 = 0;
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    v___x_2908_ = 3;
    v___x_2909_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__2);
    v___x_2910_ = lean_box((v___x_2908_) as usize);
    v___x_2911_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2911_, 0, v___x_2909_);
    lean_ctor_set(v___x_2911_, 1, v___x_2910_);
    return v___x_2911_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__5()
-> *mut LeanObject {
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    v___x_2913_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__4;
    v___x_2914_ = l_Lean_stringToMessageData(v___x_2913_);
    return v___x_2914_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__14()
-> *mut LeanObject {
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    v___x_2927_ = lean_box(0);
    v___x_2928_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__13;
    v___x_2929_ = l_Lean_mkConst(v___x_2928_, v___x_2927_);
    return v___x_2929_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__15()
-> *mut LeanObject {
    let mut v___x_2930_: u8 = 0;
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    v___x_2930_ = 1;
    v___x_2931_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__14_once), _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__14);
    v___x_2932_ = lean_box((v___x_2930_) as usize);
    v___x_2933_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2933_, 0, v___x_2931_);
    lean_ctor_set(v___x_2933_, 1, v___x_2932_);
    return v___x_2933_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey(
    mut v_type_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___y_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_a_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v_arg_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    let mut v___x_2983_: u8 = 0;
    let mut v_arg_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: u8 = 0;
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3011_: u8 = 0;
    let mut v_a_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2934_);
                v___x_2944_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_2934_, v_a_2936_);
                if lean_obj_tag(v___x_2944_) == 0 {
                    v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
                    v_isSharedCheck_3011_ = (!lean_is_exclusive(v___x_2944_)) as u8;
                    if v_isSharedCheck_3011_ == 0 {
                        v___x_2947_ = v___x_2944_;
                        v_isShared_2948_ = v_isSharedCheck_3011_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2945_);
                        lean_dec(v___x_2944_);
                        v___x_2947_ = lean_box(0);
                        v_isShared_2948_ = v_isSharedCheck_3011_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_2934_);
                    v_a_3012_ = lean_ctor_get(v___x_2944_, 0);
                    v_isSharedCheck_3019_ = (!lean_is_exclusive(v___x_2944_)) as u8;
                    if v_isSharedCheck_3019_ == 0 {
                        v___x_3014_ = v___x_2944_;
                        v_isShared_3015_ = v_isSharedCheck_3019_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3012_);
                        lean_dec(v___x_2944_);
                        v___x_3014_ = lean_box(0);
                        v_isShared_3015_ = v_isSharedCheck_3019_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2941_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__3_once), _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__3);
                v___x_2942_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2942_, 0, v_type_2934_);
                lean_ctor_set(v___x_2942_, 1, v___x_2941_);
                v___x_2943_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2943_, 0, v___x_2942_);
                return v___x_2943_;
            }
            2 => {
                v___x_2977_ = l_Lean_Expr_cleanupAnnotations(v_a_2945_);
                v___x_2978_ = l_Lean_Expr_isApp(v___x_2977_);
                if v___x_2978_ == 0 {
                    lean_dec_ref(v___x_2977_);
                    lean_del_object(v___x_2947_);
                    v___y_2950_ = v_a_2935_;
                    v___y_2951_ = v_a_2936_;
                    v___y_2952_ = v_a_2937_;
                    v___y_2953_ = v_a_2938_;
                    state = 3;
                    continue;
                } else {
                    v_arg_2979_ = lean_ctor_get(v___x_2977_, 1);
                    lean_inc_ref(v_arg_2979_);
                    v___x_2980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2977_);
                    v___x_2981_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__7;
                    v___x_2982_ = l_Lean_Expr_isConstOf(v___x_2980_, v___x_2981_);
                    if v___x_2982_ == 0 {
                        v___x_2983_ = l_Lean_Expr_isApp(v___x_2980_);
                        if v___x_2983_ == 0 {
                            lean_dec_ref(v___x_2980_);
                            lean_dec_ref(v_arg_2979_);
                            lean_del_object(v___x_2947_);
                            v___y_2950_ = v_a_2935_;
                            v___y_2951_ = v_a_2936_;
                            v___y_2952_ = v_a_2937_;
                            v___y_2953_ = v_a_2938_;
                            state = 3;
                            continue;
                        } else {
                            v_arg_2984_ = lean_ctor_get(v___x_2980_, 1);
                            lean_inc_ref(v_arg_2984_);
                            v___x_2985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2980_);
                            v___x_2986_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__9;
                            v___x_2987_ = l_Lean_Expr_isConstOf(v___x_2985_, v___x_2986_);
                            if v___x_2987_ == 0 {
                                v___x_2988_ = l_Lean_Expr_isApp(v___x_2985_);
                                if v___x_2988_ == 0 {
                                    lean_dec_ref(v___x_2985_);
                                    lean_dec_ref(v_arg_2984_);
                                    lean_dec_ref(v_arg_2979_);
                                    lean_del_object(v___x_2947_);
                                    v___y_2950_ = v_a_2935_;
                                    v___y_2951_ = v_a_2936_;
                                    v___y_2952_ = v_a_2937_;
                                    v___y_2953_ = v_a_2938_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_2989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2985_);
                                    v___x_2990_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__11;
                                    v___x_2991_ = l_Lean_Expr_isConstOf(v___x_2989_, v___x_2990_);
                                    lean_dec_ref(v___x_2989_);
                                    if v___x_2991_ == 0 {
                                        lean_dec_ref(v_arg_2984_);
                                        lean_dec_ref(v_arg_2979_);
                                        lean_del_object(v___x_2947_);
                                        v___y_2950_ = v_a_2935_;
                                        v___y_2951_ = v_a_2936_;
                                        v___y_2952_ = v_a_2937_;
                                        v___y_2953_ = v_a_2938_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_type_2934_);
                                        v___x_2992_ = 0;
                                        v___x_2993_ = lean_box((v___x_2992_) as usize);
                                        v___x_2994_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_2994_, 0, v_arg_2979_);
                                        lean_ctor_set(v___x_2994_, 1, v___x_2993_);
                                        v___x_2995_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_2995_, 0, v_arg_2984_);
                                        lean_ctor_set(v___x_2995_, 1, v___x_2994_);
                                        if v_isShared_2948_ == 0 {
                                            lean_ctor_set(v___x_2947_, 0, v___x_2995_);
                                            v___x_2997_ = v___x_2947_;
                                            state = 8;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2998_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
                                            v___x_2997_ = v_reuseFailAlloc_2998_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_2985_);
                                lean_dec_ref(v_type_2934_);
                                v___x_2999_ = 2;
                                v___x_3000_ = lean_box((v___x_2999_) as usize);
                                v___x_3001_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3001_, 0, v_arg_2979_);
                                lean_ctor_set(v___x_3001_, 1, v___x_3000_);
                                v___x_3002_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3002_, 0, v_arg_2984_);
                                lean_ctor_set(v___x_3002_, 1, v___x_3001_);
                                if v_isShared_2948_ == 0 {
                                    lean_ctor_set(v___x_2947_, 0, v___x_3002_);
                                    v___x_3004_ = v___x_2947_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
                                    v___x_3004_ = v_reuseFailAlloc_3005_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2980_);
                        lean_dec_ref(v_type_2934_);
                        v___x_3006_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__15_once), _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__15);
                        v___x_3007_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3007_, 0, v_arg_2979_);
                        lean_ctor_set(v___x_3007_, 1, v___x_3006_);
                        if v_isShared_2948_ == 0 {
                            lean_ctor_set(v___x_2947_, 0, v___x_3007_);
                            v___x_3009_ = v___x_2947_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
                            v___x_3009_ = v_reuseFailAlloc_3010_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            3 => {
                lean_inc_ref(v_type_2934_);
                v___x_2954_ = l_Lean_Meta_isProp(
                    v_type_2934_,
                    v___y_2950_,
                    v___y_2951_,
                    v___y_2952_,
                    v___y_2953_,
                );
                if lean_obj_tag(v___x_2954_) == 0 {
                    v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
                    lean_inc(v_a_2955_);
                    lean_dec_ref_known(v___x_2954_, 1);
                    v___x_2956_ = (lean_unbox(v_a_2955_) as u8);
                    lean_dec(v_a_2955_);
                    if v___x_2956_ == 0 {
                        v___x_2957_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__5_once), _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___closed__5);
                        v___x_2958_ = l_Lean_indentExpr(v_type_2934_);
                        v___x_2959_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2959_, 0, v___x_2957_);
                        lean_ctor_set(v___x_2959_, 1, v___x_2958_);
                        v___x_2960_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0___redArg(v___x_2959_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
                        v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
                        v_isSharedCheck_2968_ = (!lean_is_exclusive(v___x_2960_)) as u8;
                        if v_isSharedCheck_2968_ == 0 {
                            v___x_2963_ = v___x_2960_;
                            v_isShared_2964_ = v_isSharedCheck_2968_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2961_);
                            lean_dec(v___x_2960_);
                            v___x_2963_ = lean_box(0);
                            v_isShared_2964_ = v_isSharedCheck_2968_;
                            state = 4;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_2934_);
                    v_a_2969_ = lean_ctor_get(v___x_2954_, 0);
                    v_isSharedCheck_2976_ = (!lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2976_ == 0 {
                        v___x_2971_ = v___x_2954_;
                        v_isShared_2972_ = v_isSharedCheck_2976_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2969_);
                        lean_dec(v___x_2954_);
                        v___x_2971_ = lean_box(0);
                        v_isShared_2972_ = v_isSharedCheck_2976_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2964_ == 0 {
                    v___x_2966_ = v___x_2963_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
                    v___x_2966_ = v_reuseFailAlloc_2967_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2966_;
            }
            6 => {
                if v_isShared_2972_ == 0 {
                    v___x_2974_ = v___x_2971_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
                    v___x_2974_ = v_reuseFailAlloc_2975_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2974_;
            }
            8 => {
                return v___x_2997_;
            }
            9 => {
                return v___x_3004_;
            }
            10 => {
                return v___x_3009_;
            }
            11 => {
                if v_isShared_3015_ == 0 {
                    v___x_3017_ = v___x_3014_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
                    v___x_3017_ = v_reuseFailAlloc_3018_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey___boxed(
    mut v_type_3020_: *mut LeanObject,
    mut v_a_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3026_: *mut LeanObject = core::ptr::null_mut();
    v_res_3026_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey(
        v_type_3020_,
        v_a_3021_,
        v_a_3022_,
        v_a_3023_,
        v_a_3024_,
    );
    lean_dec(v_a_3024_);
    lean_dec_ref(v_a_3023_);
    lean_dec(v_a_3022_);
    lean_dec_ref(v_a_3021_);
    return v_res_3026_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0(
    mut v_00_u03b1_3027_: *mut LeanObject,
    mut v_msg_3028_: *mut LeanObject,
    mut v___y_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    v___x_3034_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0___redArg(v_msg_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
    return v___x_3034_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0___boxed(
    mut v_00_u03b1_3035_: *mut LeanObject,
    mut v_msg_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_selectEqKey_spec__0(v_00_u03b1_3035_, v_msg_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
    lean_dec(v___y_3040_);
    lean_dec_ref(v___y_3039_);
    lean_dec(v___y_3038_);
    lean_dec_ref(v___y_3037_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg___lam__0(
    mut v_k_3043_: *mut LeanObject,
    mut v_b_3044_: *mut LeanObject,
    mut v_c_3045_: *mut LeanObject,
    mut v___y_3046_: *mut LeanObject,
    mut v___y_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3049_);
    lean_inc_ref(v___y_3048_);
    lean_inc(v___y_3047_);
    lean_inc_ref(v___y_3046_);
    v___x_3051_ = lean_apply_7(
        v_k_3043_,
        v_b_3044_,
        v_c_3045_,
        v___y_3046_,
        v___y_3047_,
        v___y_3048_,
        v___y_3049_,
        lean_box(0),
    );
    return v___x_3051_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg___lam__0___boxed(
    mut v_k_3052_: *mut LeanObject,
    mut v_b_3053_: *mut LeanObject,
    mut v_c_3054_: *mut LeanObject,
    mut v___y_3055_: *mut LeanObject,
    mut v___y_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3060_: *mut LeanObject = core::ptr::null_mut();
    v_res_3060_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg___lam__0(v_k_3052_, v_b_3053_, v_c_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
    lean_dec(v___y_3058_);
    lean_dec_ref(v___y_3057_);
    lean_dec(v___y_3056_);
    lean_dec_ref(v___y_3055_);
    return v_res_3060_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg(
    mut v_type_3061_: *mut LeanObject,
    mut v_maxFVars_x3f_3062_: *mut LeanObject,
    mut v_k_3063_: *mut LeanObject,
    mut v_cleanupAnnotations_3064_: u8,
    mut v_whnfType_3065_: u8,
    mut v___y_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
    mut v___y_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_a_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3071_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3071_, 0, v_k_3063_);
                v___x_3072_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_3061_,
                    v_maxFVars_x3f_3062_,
                    v___f_3071_,
                    v_cleanupAnnotations_3064_,
                    v_whnfType_3065_,
                    v___y_3066_,
                    v___y_3067_,
                    v___y_3068_,
                    v___y_3069_,
                );
                if lean_obj_tag(v___x_3072_) == 0 {
                    v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
                    v_isSharedCheck_3080_ = (!lean_is_exclusive(v___x_3072_)) as u8;
                    if v_isSharedCheck_3080_ == 0 {
                        v___x_3075_ = v___x_3072_;
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3073_);
                        lean_dec(v___x_3072_);
                        v___x_3075_ = lean_box(0);
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3081_ = lean_ctor_get(v___x_3072_, 0);
                    v_isSharedCheck_3088_ = (!lean_is_exclusive(v___x_3072_)) as u8;
                    if v_isSharedCheck_3088_ == 0 {
                        v___x_3083_ = v___x_3072_;
                        v_isShared_3084_ = v_isSharedCheck_3088_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3081_);
                        lean_dec(v___x_3072_);
                        v___x_3083_ = lean_box(0);
                        v_isShared_3084_ = v_isSharedCheck_3088_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3076_ == 0 {
                    v___x_3078_ = v___x_3075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
                    v___x_3078_ = v_reuseFailAlloc_3079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3078_;
            }
            3 => {
                if v_isShared_3084_ == 0 {
                    v___x_3086_ = v___x_3083_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
                    v___x_3086_ = v_reuseFailAlloc_3087_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg___boxed(
    mut v_type_3089_: *mut LeanObject,
    mut v_maxFVars_x3f_3090_: *mut LeanObject,
    mut v_k_3091_: *mut LeanObject,
    mut v_cleanupAnnotations_3092_: *mut LeanObject,
    mut v_whnfType_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3099_: u8 = 0;
    let mut v_whnfType_boxed_3100_: u8 = 0;
    let mut v_res_3101_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3099_ = (lean_unbox(v_cleanupAnnotations_3092_) as u8);
    v_whnfType_boxed_3100_ = (lean_unbox(v_whnfType_3093_) as u8);
    v_res_3101_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg(v_type_3089_, v_maxFVars_x3f_3090_, v_k_3091_, v_cleanupAnnotations_boxed_3099_, v_whnfType_boxed_3100_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
    lean_dec(v___y_3097_);
    lean_dec_ref(v___y_3096_);
    lean_dec(v___y_3095_);
    lean_dec_ref(v___y_3094_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0(
    mut v_00_u03b1_3102_: *mut LeanObject,
    mut v_type_3103_: *mut LeanObject,
    mut v_maxFVars_x3f_3104_: *mut LeanObject,
    mut v_k_3105_: *mut LeanObject,
    mut v_cleanupAnnotations_3106_: u8,
    mut v_whnfType_3107_: u8,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    v___x_3113_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg(v_type_3103_, v_maxFVars_x3f_3104_, v_k_3105_, v_cleanupAnnotations_3106_, v_whnfType_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
    return v___x_3113_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___boxed(
    mut v_00_u03b1_3114_: *mut LeanObject,
    mut v_type_3115_: *mut LeanObject,
    mut v_maxFVars_x3f_3116_: *mut LeanObject,
    mut v_k_3117_: *mut LeanObject,
    mut v_cleanupAnnotations_3118_: *mut LeanObject,
    mut v_whnfType_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3125_: u8 = 0;
    let mut v_whnfType_boxed_3126_: u8 = 0;
    let mut v_res_3127_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3125_ = (lean_unbox(v_cleanupAnnotations_3118_) as u8);
    v_whnfType_boxed_3126_ = (lean_unbox(v_whnfType_3119_) as u8);
    v_res_3127_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0(v_00_u03b1_3114_, v_type_3115_, v_maxFVars_x3f_3116_, v_k_3117_, v_cleanupAnnotations_boxed_3125_, v_whnfType_boxed_3126_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
    lean_dec(v___y_3123_);
    lean_dec_ref(v___y_3122_);
    lean_dec(v___y_3121_);
    lean_dec_ref(v___y_3120_);
    return v_res_3127_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner___lam__0(
    mut v_expr_3128_: *mut LeanObject,
    mut v_wrap_3129_: *mut LeanObject,
    mut v_xs_3130_: *mut LeanObject,
    mut v_x_3131_: *mut LeanObject,
    mut v___y_3132_: *mut LeanObject,
    mut v___y_3133_: *mut LeanObject,
    mut v___y_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    v___x_3137_ = l_Lean_mkAppN(v_expr_3128_, v_xs_3130_);
    lean_inc(v___y_3135_);
    lean_inc_ref(v___y_3134_);
    lean_inc(v___y_3133_);
    lean_inc_ref(v___y_3132_);
    v___x_3138_ = lean_apply_6(
        v_wrap_3129_,
        v___x_3137_,
        v___y_3132_,
        v___y_3133_,
        v___y_3134_,
        v___y_3135_,
        lean_box(0),
    );
    if lean_obj_tag(v___x_3138_) == 0 {
        let mut v_a_3139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3140_: u8 = 0;
        let mut v___x_3141_: u8 = 0;
        let mut v___x_3142_: u8 = 0;
        let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
        v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
        lean_inc(v_a_3139_);
        lean_dec_ref_known(v___x_3138_, 1);
        v___x_3140_ = 0;
        v___x_3141_ = 1;
        v___x_3142_ = 1;
        v___x_3143_ = l_Lean_Meta_mkLambdaFVars(
            v_xs_3130_,
            v_a_3139_,
            v___x_3140_,
            v___x_3141_,
            v___x_3140_,
            v___x_3141_,
            v___x_3142_,
            v___y_3132_,
            v___y_3133_,
            v___y_3134_,
            v___y_3135_,
        );
        return v___x_3143_;
    } else {
        return v___x_3138_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner___lam__0___boxed(
    mut v_expr_3144_: *mut LeanObject,
    mut v_wrap_3145_: *mut LeanObject,
    mut v_xs_3146_: *mut LeanObject,
    mut v_x_3147_: *mut LeanObject,
    mut v___y_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3153_: *mut LeanObject = core::ptr::null_mut();
    v_res_3153_ =
        l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner___lam__0(
            v_expr_3144_,
            v_wrap_3145_,
            v_xs_3146_,
            v_x_3147_,
            v___y_3148_,
            v___y_3149_,
            v___y_3150_,
            v___y_3151_,
        );
    lean_dec(v___y_3151_);
    lean_dec_ref(v___y_3150_);
    lean_dec(v___y_3149_);
    lean_dec_ref(v___y_3148_);
    lean_dec_ref(v_x_3147_);
    lean_dec_ref(v_xs_3146_);
    return v_res_3153_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner(
    mut v_numVars_3154_: *mut LeanObject,
    mut v_expr_3155_: *mut LeanObject,
    mut v_wrap_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___f_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u8 = 0;
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3160_);
                lean_inc_ref(v_a_3159_);
                lean_inc(v_a_3158_);
                lean_inc_ref(v_a_3157_);
                lean_inc_ref(v_expr_3155_);
                v___x_3162_ =
                    lean_infer_type(v_expr_3155_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
                if lean_obj_tag(v___x_3162_) == 0 {
                    v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
                    v_isSharedCheck_3173_ = (!lean_is_exclusive(v___x_3162_)) as u8;
                    if v_isSharedCheck_3173_ == 0 {
                        v___x_3165_ = v___x_3162_;
                        v_isShared_3166_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3163_);
                        lean_dec(v___x_3162_);
                        v___x_3165_ = lean_box(0);
                        v_isShared_3166_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_wrap_3156_);
                    lean_dec_ref(v_expr_3155_);
                    lean_dec(v_numVars_3154_);
                    return v___x_3162_;
                }
            }
            1 => {
                v___f_3167_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                lean_closure_set(v___f_3167_, 0, v_expr_3155_);
                lean_closure_set(v___f_3167_, 1, v_wrap_3156_);
                if v_isShared_3166_ == 0 {
                    lean_ctor_set_tag(v___x_3165_, 1);
                    lean_ctor_set(v___x_3165_, 0, v_numVars_3154_);
                    v___x_3169_ = v___x_3165_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_numVars_3154_);
                    v___x_3169_ = v_reuseFailAlloc_3172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3170_ = 0;
                v___x_3171_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner_spec__0___redArg(v_a_3163_, v___x_3169_, v___f_3167_, v___x_3170_, v___x_3170_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
                return v___x_3171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner___boxed(
    mut v_numVars_3174_: *mut LeanObject,
    mut v_expr_3175_: *mut LeanObject,
    mut v_wrap_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
    mut v_a_3179_: *mut LeanObject,
    mut v_a_3180_: *mut LeanObject,
    mut v_a_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3182_: *mut LeanObject = core::ptr::null_mut();
    v_res_3182_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner(
        v_numVars_3174_,
        v_expr_3175_,
        v_wrap_3176_,
        v_a_3177_,
        v_a_3178_,
        v_a_3179_,
        v_a_3180_,
    );
    lean_dec(v_a_3180_);
    lean_dec_ref(v_a_3179_);
    lean_dec(v_a_3178_);
    lean_dec_ref(v_a_3177_);
    return v_res_3182_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0(
    mut v_h_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    v___x_3192_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___closed__1;
    v___x_3193_ = lean_unsigned_to_nat(1);
    v___x_3194_ = lean_mk_empty_array_with_capacity(v___x_3193_);
    v___x_3195_ = lean_array_push(v___x_3194_, v_h_3186_);
    v___x_3196_ = l_Lean_Meta_mkAppM(
        v___x_3192_,
        v___x_3195_,
        v___y_3187_,
        v___y_3188_,
        v___y_3189_,
        v___y_3190_,
    );
    return v___x_3196_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0___boxed(
    mut v_h_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
    mut v___y_3199_: *mut LeanObject,
    mut v___y_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3203_: *mut LeanObject = core::ptr::null_mut();
    v_res_3203_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__0(
        v_h_3197_,
        v___y_3198_,
        v___y_3199_,
        v___y_3200_,
        v___y_3201_,
    );
    lean_dec(v___y_3201_);
    lean_dec_ref(v___y_3200_);
    lean_dec(v___y_3199_);
    lean_dec_ref(v___y_3198_);
    return v_res_3203_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1(
    mut v_h_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
    mut v___y_3211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    v___x_3213_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___closed__1;
    v___x_3214_ = lean_unsigned_to_nat(1);
    v___x_3215_ = lean_mk_empty_array_with_capacity(v___x_3214_);
    v___x_3216_ = lean_array_push(v___x_3215_, v_h_3207_);
    v___x_3217_ = l_Lean_Meta_mkAppM(
        v___x_3213_,
        v___x_3216_,
        v___y_3208_,
        v___y_3209_,
        v___y_3210_,
        v___y_3211_,
    );
    return v___x_3217_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1___boxed(
    mut v_h_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3224_: *mut LeanObject = core::ptr::null_mut();
    v_res_3224_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__1(
        v_h_3218_,
        v___y_3219_,
        v___y_3220_,
        v___y_3221_,
        v___y_3222_,
    );
    lean_dec(v___y_3222_);
    lean_dec_ref(v___y_3221_);
    lean_dec(v___y_3220_);
    lean_dec_ref(v___y_3219_);
    return v_res_3224_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2(
    mut v_h_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    v___x_3234_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___closed__1;
    v___x_3235_ = lean_unsigned_to_nat(1);
    v___x_3236_ = lean_mk_empty_array_with_capacity(v___x_3235_);
    v___x_3237_ = lean_array_push(v___x_3236_, v_h_3228_);
    v___x_3238_ = l_Lean_Meta_mkAppM(
        v___x_3234_,
        v___x_3237_,
        v___y_3229_,
        v___y_3230_,
        v___y_3231_,
        v___y_3232_,
    );
    return v___x_3238_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2___boxed(
    mut v_h_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
    mut v___y_3241_: *mut LeanObject,
    mut v___y_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3245_: *mut LeanObject = core::ptr::null_mut();
    v_res_3245_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___lam__2(
        v_h_3239_,
        v___y_3240_,
        v___y_3241_,
        v___y_3242_,
        v___y_3243_,
    );
    lean_dec(v___y_3243_);
    lean_dec_ref(v___y_3242_);
    lean_dec(v___y_3241_);
    lean_dec_ref(v___y_3240_);
    return v_res_3245_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof(
    mut v_numVars_3249_: *mut LeanObject,
    mut v_expr_3250_: *mut LeanObject,
    mut v_adaptation_3251_: u8,
    mut v_a_3252_: *mut LeanObject,
    mut v_a_3253_: *mut LeanObject,
    mut v_a_3254_: *mut LeanObject,
    mut v_a_3255_: *mut LeanObject,
) -> *mut LeanObject {
    match v_adaptation_3251_ {
        0 => {
            let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_numVars_3249_);
            v___x_3257_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_3257_, 0, v_expr_3250_);
            return v___x_3257_;
        }
        1 => {
            let mut v___f_3258_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
            v___f_3258_ =
                l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__0;
            v___x_3259_ =
                l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner(
                    v_numVars_3249_,
                    v_expr_3250_,
                    v___f_3258_,
                    v_a_3252_,
                    v_a_3253_,
                    v_a_3254_,
                    v_a_3255_,
                );
            return v___x_3259_;
        }
        2 => {
            let mut v___f_3260_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
            v___f_3260_ =
                l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__1;
            v___x_3261_ =
                l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner(
                    v_numVars_3249_,
                    v_expr_3250_,
                    v___f_3260_,
                    v_a_3252_,
                    v_a_3253_,
                    v_a_3254_,
                    v_a_3255_,
                );
            return v___x_3261_;
        }
        _ => {
            let mut v___f_3262_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
            v___f_3262_ =
                l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___closed__2;
            v___x_3263_ =
                l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof_wrapInner(
                    v_numVars_3249_,
                    v_expr_3250_,
                    v___f_3262_,
                    v_a_3252_,
                    v_a_3253_,
                    v_a_3254_,
                    v_a_3255_,
                );
            return v___x_3263_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof___boxed(
    mut v_numVars_3264_: *mut LeanObject,
    mut v_expr_3265_: *mut LeanObject,
    mut v_adaptation_3266_: *mut LeanObject,
    mut v_a_3267_: *mut LeanObject,
    mut v_a_3268_: *mut LeanObject,
    mut v_a_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
    mut v_a_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_adaptation_boxed_3272_: u8 = 0;
    let mut v_res_3273_: *mut LeanObject = core::ptr::null_mut();
    v_adaptation_boxed_3272_ = (lean_unbox(v_adaptation_3266_) as u8);
    v_res_3273_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof(
        v_numVars_3264_,
        v_expr_3265_,
        v_adaptation_boxed_3272_,
        v_a_3267_,
        v_a_3268_,
        v_a_3269_,
        v_a_3270_,
    );
    lean_dec(v_a_3270_);
    lean_dec_ref(v_a_3269_);
    lean_dec(v_a_3268_);
    lean_dec_ref(v_a_3267_);
    return v_res_3273_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
    mut v_declName_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
    mut v_a_3279_: *mut LeanObject,
    mut v_a_3280_: *mut LeanObject,
    mut v_a_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varTypes_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pattern_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: u8 = 0;
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3311_: u8 = 0;
    let mut v_a_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_a_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut v_a_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_3277_);
                v___x_3283_ =
                    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern(
                        v_declName_3277_,
                        v_a_3278_,
                        v_a_3279_,
                        v_a_3280_,
                        v_a_3281_,
                    );
                if lean_obj_tag(v___x_3283_) == 0 {
                    v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
                    lean_inc(v_a_3284_);
                    lean_dec_ref_known(v___x_3283_, 1);
                    v_fst_3285_ = lean_ctor_get(v_a_3284_, 0);
                    lean_inc(v_fst_3285_);
                    v_snd_3286_ = lean_ctor_get(v_a_3284_, 1);
                    lean_inc_n(v_snd_3286_, 2);
                    lean_dec(v_a_3284_);
                    v___x_3287_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__0;
                    v___x_3288_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__1;
                    v___x_3289_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_box(0), v_fst_3285_, v_snd_3286_, v___x_3287_, v_snd_3286_, v___x_3288_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
                    if lean_obj_tag(v___x_3289_) == 0 {
                        v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
                        lean_inc(v_a_3290_);
                        lean_dec_ref_known(v___x_3289_, 1);
                        v_snd_3291_ = lean_ctor_get(v_a_3290_, 1);
                        lean_inc(v_snd_3291_);
                        v_fst_3292_ = lean_ctor_get(v_a_3290_, 0);
                        lean_inc(v_fst_3292_);
                        lean_dec(v_a_3290_);
                        v_fst_3293_ = lean_ctor_get(v_snd_3291_, 0);
                        lean_inc(v_fst_3293_);
                        v_snd_3294_ = lean_ctor_get(v_snd_3291_, 1);
                        lean_inc(v_snd_3294_);
                        lean_dec(v_snd_3291_);
                        v_varTypes_3295_ = lean_ctor_get(v_fst_3292_, 1);
                        v_pattern_3296_ = lean_ctor_get(v_fst_3292_, 3);
                        v___x_3297_ = lean_array_get_size(v_varTypes_3295_);
                        v___x_3298_ = lean_box(0);
                        v___x_3299_ = l_Lean_mkConst(v_declName_3277_, v___x_3298_);
                        v___x_3300_ = (lean_unbox(v_snd_3294_) as u8);
                        lean_dec(v_snd_3294_);
                        v___x_3301_ =
                            l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof(
                                v___x_3297_,
                                v___x_3299_,
                                v___x_3300_,
                                v_a_3278_,
                                v_a_3279_,
                                v_a_3280_,
                                v_a_3281_,
                            );
                        if lean_obj_tag(v___x_3301_) == 0 {
                            v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
                            v_isSharedCheck_3311_ = (!lean_is_exclusive(v___x_3301_)) as u8;
                            if v_isSharedCheck_3311_ == 0 {
                                v___x_3304_ = v___x_3301_;
                                v_isShared_3305_ = v_isSharedCheck_3311_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3302_);
                                lean_dec(v___x_3301_);
                                v___x_3304_ = lean_box(0);
                                v_isShared_3305_ = v_isSharedCheck_3311_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_3293_);
                            lean_dec(v_fst_3292_);
                            v_a_3312_ = lean_ctor_get(v___x_3301_, 0);
                            v_isSharedCheck_3319_ = (!lean_is_exclusive(v___x_3301_)) as u8;
                            if v_isSharedCheck_3319_ == 0 {
                                v___x_3314_ = v___x_3301_;
                                v_isShared_3315_ = v_isSharedCheck_3319_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3312_);
                                lean_dec(v___x_3301_);
                                v___x_3314_ = lean_box(0);
                                v_isShared_3315_ = v_isSharedCheck_3319_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_declName_3277_);
                        v_a_3320_ = lean_ctor_get(v___x_3289_, 0);
                        v_isSharedCheck_3327_ = (!lean_is_exclusive(v___x_3289_)) as u8;
                        if v_isSharedCheck_3327_ == 0 {
                            v___x_3322_ = v___x_3289_;
                            v_isShared_3323_ = v_isSharedCheck_3327_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3320_);
                            lean_dec(v___x_3289_);
                            v___x_3322_ = lean_box(0);
                            v_isShared_3323_ = v_isSharedCheck_3327_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_3277_);
                    v_a_3328_ = lean_ctor_get(v___x_3283_, 0);
                    v_isSharedCheck_3335_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                    if v_isSharedCheck_3335_ == 0 {
                        v___x_3330_ = v___x_3283_;
                        v_isShared_3331_ = v_isSharedCheck_3335_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3328_);
                        lean_dec(v___x_3283_);
                        v___x_3330_ = lean_box(0);
                        v_isShared_3331_ = v_isSharedCheck_3335_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3306_ =
                    l_Lean_Meta_Sym_Simp_isPerm(v___x_3297_, v_pattern_3296_, v_fst_3293_);
                v___x_3307_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3307_, 0, v_a_3302_);
                lean_ctor_set(v___x_3307_, 1, v_fst_3292_);
                lean_ctor_set(v___x_3307_, 2, v_fst_3293_);
                lean_ctor_set_uint8(
                    v___x_3307_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3306_,
                );
                if v_isShared_3305_ == 0 {
                    lean_ctor_set(v___x_3304_, 0, v___x_3307_);
                    v___x_3309_ = v___x_3304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
                    v___x_3309_ = v_reuseFailAlloc_3310_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3309_;
            }
            3 => {
                if v_isShared_3315_ == 0 {
                    v___x_3317_ = v___x_3314_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
                    v___x_3317_ = v_reuseFailAlloc_3318_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3317_;
            }
            5 => {
                if v_isShared_3323_ == 0 {
                    v___x_3325_ = v___x_3322_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
                    v___x_3325_ = v_reuseFailAlloc_3326_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3325_;
            }
            7 => {
                if v_isShared_3331_ == 0 {
                    v___x_3333_ = v___x_3330_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
                    v___x_3333_ = v_reuseFailAlloc_3334_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___boxed(
    mut v_declName_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
    mut v_a_3338_: *mut LeanObject,
    mut v_a_3339_: *mut LeanObject,
    mut v_a_3340_: *mut LeanObject,
    mut v_a_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3342_: *mut LeanObject = core::ptr::null_mut();
    v_res_3342_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
        v_declName_3336_,
        v_a_3337_,
        v_a_3338_,
        v_a_3339_,
        v_a_3340_,
    );
    lean_dec(v_a_3340_);
    lean_dec_ref(v_a_3339_);
    lean_dec(v_a_3338_);
    lean_dec_ref(v_a_3337_);
    return v_res_3342_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(
    mut v_e_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
    mut v_a_3345_: *mut LeanObject,
    mut v_a_3346_: *mut LeanObject,
    mut v_a_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varTypes_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pattern_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3376_: u8 = 0;
    let mut v_a_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_a_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3388_: u8 = 0;
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut v_a_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3396_: u8 = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3349_ = lean_box(0);
                lean_inc_ref(v_e_3343_);
                v___x_3350_ =
                    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern(
                        v_e_3343_,
                        v___x_3349_,
                        v_a_3344_,
                        v_a_3345_,
                        v_a_3346_,
                        v_a_3347_,
                    );
                if lean_obj_tag(v___x_3350_) == 0 {
                    v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
                    lean_inc(v_a_3351_);
                    lean_dec_ref_known(v___x_3350_, 1);
                    v_fst_3352_ = lean_ctor_get(v_a_3351_, 0);
                    lean_inc(v_fst_3352_);
                    v_snd_3353_ = lean_ctor_get(v_a_3351_, 1);
                    lean_inc_n(v_snd_3353_, 2);
                    lean_dec(v_a_3351_);
                    v___x_3354_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__0;
                    v___x_3355_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl___closed__1;
                    v___x_3356_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_box(0), v_fst_3352_, v_snd_3353_, v___x_3354_, v_snd_3353_, v___x_3355_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
                    if lean_obj_tag(v___x_3356_) == 0 {
                        v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
                        lean_inc(v_a_3357_);
                        lean_dec_ref_known(v___x_3356_, 1);
                        v_snd_3358_ = lean_ctor_get(v_a_3357_, 1);
                        lean_inc(v_snd_3358_);
                        v_fst_3359_ = lean_ctor_get(v_a_3357_, 0);
                        lean_inc(v_fst_3359_);
                        lean_dec(v_a_3357_);
                        v_fst_3360_ = lean_ctor_get(v_snd_3358_, 0);
                        lean_inc(v_fst_3360_);
                        v_snd_3361_ = lean_ctor_get(v_snd_3358_, 1);
                        lean_inc(v_snd_3361_);
                        lean_dec(v_snd_3358_);
                        v_varTypes_3362_ = lean_ctor_get(v_fst_3359_, 1);
                        v_pattern_3363_ = lean_ctor_get(v_fst_3359_, 3);
                        v___x_3364_ = lean_array_get_size(v_varTypes_3362_);
                        v___x_3365_ = (lean_unbox(v_snd_3361_) as u8);
                        lean_dec(v_snd_3361_);
                        v___x_3366_ =
                            l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_wrapProof(
                                v___x_3364_,
                                v_e_3343_,
                                v___x_3365_,
                                v_a_3344_,
                                v_a_3345_,
                                v_a_3346_,
                                v_a_3347_,
                            );
                        if lean_obj_tag(v___x_3366_) == 0 {
                            v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
                            v_isSharedCheck_3376_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                            if v_isSharedCheck_3376_ == 0 {
                                v___x_3369_ = v___x_3366_;
                                v_isShared_3370_ = v_isSharedCheck_3376_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3367_);
                                lean_dec(v___x_3366_);
                                v___x_3369_ = lean_box(0);
                                v_isShared_3370_ = v_isSharedCheck_3376_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_3360_);
                            lean_dec(v_fst_3359_);
                            v_a_3377_ = lean_ctor_get(v___x_3366_, 0);
                            v_isSharedCheck_3384_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                            if v_isSharedCheck_3384_ == 0 {
                                v___x_3379_ = v___x_3366_;
                                v_isShared_3380_ = v_isSharedCheck_3384_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3377_);
                                lean_dec(v___x_3366_);
                                v___x_3379_ = lean_box(0);
                                v_isShared_3380_ = v_isSharedCheck_3384_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_3343_);
                        v_a_3385_ = lean_ctor_get(v___x_3356_, 0);
                        v_isSharedCheck_3392_ = (!lean_is_exclusive(v___x_3356_)) as u8;
                        if v_isSharedCheck_3392_ == 0 {
                            v___x_3387_ = v___x_3356_;
                            v_isShared_3388_ = v_isSharedCheck_3392_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3385_);
                            lean_dec(v___x_3356_);
                            v___x_3387_ = lean_box(0);
                            v_isShared_3388_ = v_isSharedCheck_3392_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_3343_);
                    v_a_3393_ = lean_ctor_get(v___x_3350_, 0);
                    v_isSharedCheck_3400_ = (!lean_is_exclusive(v___x_3350_)) as u8;
                    if v_isSharedCheck_3400_ == 0 {
                        v___x_3395_ = v___x_3350_;
                        v_isShared_3396_ = v_isSharedCheck_3400_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3393_);
                        lean_dec(v___x_3350_);
                        v___x_3395_ = lean_box(0);
                        v_isShared_3396_ = v_isSharedCheck_3400_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3371_ =
                    l_Lean_Meta_Sym_Simp_isPerm(v___x_3364_, v_pattern_3363_, v_fst_3360_);
                v___x_3372_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3372_, 0, v_a_3367_);
                lean_ctor_set(v___x_3372_, 1, v_fst_3359_);
                lean_ctor_set(v___x_3372_, 2, v_fst_3360_);
                lean_ctor_set_uint8(
                    v___x_3372_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3371_,
                );
                if v_isShared_3370_ == 0 {
                    lean_ctor_set(v___x_3369_, 0, v___x_3372_);
                    v___x_3374_ = v___x_3369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
                    v___x_3374_ = v_reuseFailAlloc_3375_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3374_;
            }
            3 => {
                if v_isShared_3380_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3382_;
            }
            5 => {
                if v_isShared_3388_ == 0 {
                    v___x_3390_ = v___x_3387_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
                    v___x_3390_ = v_reuseFailAlloc_3391_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3390_;
            }
            7 => {
                if v_isShared_3396_ == 0 {
                    v___x_3398_ = v___x_3395_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
                    v___x_3398_ = v_reuseFailAlloc_3399_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkTheoremFromExpr___boxed(
    mut v_e_3401_: *mut LeanObject,
    mut v_a_3402_: *mut LeanObject,
    mut v_a_3403_: *mut LeanObject,
    mut v_a_3404_: *mut LeanObject,
    mut v_a_3405_: *mut LeanObject,
    mut v_a_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3407_: *mut LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(
        v_e_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_,
    );
    lean_dec(v_a_3405_);
    lean_dec_ref(v_a_3404_);
    lean_dec(v_a_3403_);
    lean_dec_ref(v_a_3402_);
    return v_res_3407_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(
    mut v_ext_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    v___x_3411_ = lean_st_ref_get(v_a_3409_);
    v_ext_3412_ = lean_ctor_get(v_ext_3408_, 1);
    v_toEnvExtension_3413_ = lean_ctor_get(v_ext_3412_, 0);
    v_env_3414_ = lean_ctor_get(v___x_3411_, 0);
    lean_inc_ref(v_env_3414_);
    lean_dec(v___x_3411_);
    v_asyncMode_3415_ = lean_ctor_get(v_toEnvExtension_3413_, 2);
    v___x_3416_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default;
    v___x_3417_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_3416_,
        v_ext_3408_,
        v_env_3414_,
        v_asyncMode_3415_,
    );
    v___x_3418_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3418_, 0, v___x_3417_);
    return v___x_3418_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg___boxed(
    mut v_ext_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3422_: *mut LeanObject = core::ptr::null_mut();
    v_res_3422_ =
        l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v_ext_3419_, v_a_3420_);
    lean_dec(v_a_3420_);
    lean_dec_ref(v_ext_3419_);
    return v_res_3422_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems(
    mut v_ext_3423_: *mut LeanObject,
    mut v_a_3424_: *mut LeanObject,
    mut v_a_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v___x_3427_ =
        l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v_ext_3423_, v_a_3425_);
    return v___x_3427_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___boxed(
    mut v_ext_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
    mut v_a_3430_: *mut LeanObject,
    mut v_a_3431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3432_: *mut LeanObject = core::ptr::null_mut();
    v_res_3432_ =
        l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems(v_ext_3428_, v_a_3429_, v_a_3430_);
    lean_dec(v_a_3430_);
    lean_dec_ref(v_a_3429_);
    lean_dec_ref(v_ext_3428_);
    return v_res_3432_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    v___x_3459_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__10;
    v___x_3460_ = l_Lean_mkAtom(v___x_3459_);
    return v___x_3460_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    v___x_3461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__12_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__12,
    );
    v___x_3462_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5;
    v___x_3463_ = lean_array_push(v___x_3462_, v___x_3461_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    v___x_3472_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__17;
    v___x_3473_ = l_Lean_mkAtom(v___x_3472_);
    return v___x_3473_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    v___x_3474_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__18_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__18,
    );
    v___x_3475_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5;
    v___x_3476_ = lean_array_push(v___x_3475_, v___x_3474_);
    return v___x_3476_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    v___x_3477_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__19_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__19,
    );
    v___x_3478_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__16;
    v___x_3479_ = lean_box(2);
    v___x_3480_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3480_, 0, v___x_3479_);
    lean_ctor_set(v___x_3480_, 1, v___x_3478_);
    lean_ctor_set(v___x_3480_, 2, v___x_3477_);
    return v___x_3480_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__20_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__20,
    );
    v___x_3482_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__13_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__13,
    );
    v___x_3483_ = lean_array_push(v___x_3482_, v___x_3481_);
    return v___x_3483_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__21_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__21,
    );
    v___x_3485_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__11;
    v___x_3486_ = lean_box(2);
    v___x_3487_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3487_, 0, v___x_3486_);
    lean_ctor_set(v___x_3487_, 1, v___x_3485_);
    lean_ctor_set(v___x_3487_, 2, v___x_3484_);
    return v___x_3487_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    v___x_3488_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__22_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__22,
    );
    v___x_3489_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5;
    v___x_3490_ = lean_array_push(v___x_3489_, v___x_3488_);
    return v___x_3490_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    v___x_3491_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__23_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__23,
    );
    v___x_3492_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__9;
    v___x_3493_ = lean_box(2);
    v___x_3494_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3494_, 0, v___x_3493_);
    lean_ctor_set(v___x_3494_, 1, v___x_3492_);
    lean_ctor_set(v___x_3494_, 2, v___x_3491_);
    return v___x_3494_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    v___x_3495_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__24_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__24,
    );
    v___x_3496_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5;
    v___x_3497_ = lean_array_push(v___x_3496_, v___x_3495_);
    return v___x_3497_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    v___x_3498_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__25_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__25,
    );
    v___x_3499_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__7;
    v___x_3500_ = lean_box(2);
    v___x_3501_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3501_, 0, v___x_3500_);
    lean_ctor_set(v___x_3501_, 1, v___x_3499_);
    lean_ctor_set(v___x_3501_, 2, v___x_3498_);
    return v___x_3501_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    v___x_3502_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__26_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__26,
    );
    v___x_3503_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__5;
    v___x_3504_ = lean_array_push(v___x_3503_, v___x_3502_);
    return v___x_3504_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v___x_3505_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__27_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__27,
    );
    v___x_3506_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__4;
    v___x_3507_ = lean_box(2);
    v___x_3508_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3508_, 0, v___x_3507_);
    lean_ctor_set(v___x_3508_, 1, v___x_3506_);
    lean_ctor_set(v___x_3508_, 2, v___x_3505_);
    return v___x_3508_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1() -> *mut LeanObject {
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    v___x_3509_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__28_once),
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1___closed__28,
    );
    return v___x_3509_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__0(
    mut v_x_3510_: *mut LeanObject,
    mut v_thm_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_3512_: *mut LeanObject = core::ptr::null_mut();
    v_expr_3512_ = lean_ctor_get(v_thm_3511_, 0);
    if lean_obj_tag(v_expr_3512_) == 4 {
        let mut v_declName_3513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3514_: u8 = 0;
        v_declName_3513_ = lean_ctor_get(v_expr_3512_, 0);
        v___x_3514_ = l_Lean_isPrivateName(v_declName_3513_);
        if v___x_3514_ == 0 {
            let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
            v___x_3515_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3515_, 0, v_thm_3511_);
            lean_inc_ref_n(v___x_3515_, 2);
            v___x_3516_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_3516_, 0, v___x_3515_);
            lean_ctor_set(v___x_3516_, 1, v___x_3515_);
            lean_ctor_set(v___x_3516_, 2, v___x_3515_);
            return v___x_3516_;
        } else {
            let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
            v___x_3517_ = lean_box(0);
            v___x_3518_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3518_, 0, v_thm_3511_);
            v___x_3519_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_3519_, 0, v___x_3517_);
            lean_ctor_set(v___x_3519_, 1, v___x_3517_);
            lean_ctor_set(v___x_3519_, 2, v___x_3518_);
            return v___x_3519_;
        }
    } else {
        let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
        v___x_3520_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3520_, 0, v_thm_3511_);
        lean_inc_ref_n(v___x_3520_, 2);
        v___x_3521_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_3521_, 0, v___x_3520_);
        lean_ctor_set(v___x_3521_, 1, v___x_3520_);
        lean_ctor_set(v___x_3521_, 2, v___x_3520_);
        return v___x_3521_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__0___boxed(
    mut v_x_3522_: *mut LeanObject,
    mut v_thm_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3524_: *mut LeanObject = core::ptr::null_mut();
    v_res_3524_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__0(v_x_3522_, v_thm_3523_);
    lean_dec_ref(v_x_3522_);
    return v_res_3524_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__1(
    mut v___y_3525_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_3525_);
    return v___y_3525_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__1___boxed(
    mut v___y_3526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3527_: *mut LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___lam__1(v___y_3526_);
    lean_dec_ref(v___y_3526_);
    return v_res_3527_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpExt(
    mut v_name_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    v___f_3533_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__0;
    v___f_3534_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__1;
    v___f_3535_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt___closed__2;
    v___x_3536_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1_once
        ),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default___closed__1,
    );
    v___x_3537_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3537_, 0, v_name_3531_);
    lean_ctor_set(v___x_3537_, 1, v___f_3533_);
    lean_ctor_set(v___x_3537_, 2, v___x_3536_);
    lean_ctor_set(v___x_3537_, 3, v___f_3535_);
    lean_ctor_set(v___x_3537_, 4, v___f_3534_);
    v___x_3538_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3537_);
    return v___x_3538_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkSymSimpExt___boxed(
    mut v_name_3539_: *mut LeanObject,
    mut v_a_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3541_: *mut LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v_name_3539_);
    return v_res_3541_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    v___x_3542_ = lean_box(0);
    v___x_3543_ = lean_unsigned_to_nat(16);
    v___x_3544_ = lean_mk_array(v___x_3543_, v___x_3542_);
    return v___x_3544_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    v___x_3545_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_);
    v___x_3546_ = lean_unsigned_to_nat(0);
    v___x_3547_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3547_, 0, v___x_3546_);
    lean_ctor_set(v___x_3547_, 1, v___x_3545_);
    return v___x_3547_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    v___x_3549_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_);
    v___x_3550_ = lean_st_mk_ref(v___x_3549_);
    v___x_3551_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3551_, 0, v___x_3550_);
    return v___x_3551_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2____boxed(
    mut v_a_3552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3553_: *mut LeanObject = core::ptr::null_mut();
    v_res_3553_ = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_();
    return v_res_3553_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_keys_3554_: *mut LeanObject,
    mut v_i_3555_: *mut LeanObject,
    mut v_k_3556_: *mut LeanObject,
) -> u8 {
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v_k_x27_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3557_ = lean_array_get_size(v_keys_3554_);
                v___x_3558_ = lean_nat_dec_lt(v_i_3555_, v___x_3557_);
                if v___x_3558_ == 0 {
                    lean_dec(v_i_3555_);
                    return v___x_3558_;
                } else {
                    v_k_x27_3559_ = lean_array_fget_borrowed(v_keys_3554_, v_i_3555_);
                    v___x_3560_ = l_Lean_instBEqExtraModUse_beq(v_k_3556_, v_k_x27_3559_);
                    if v___x_3560_ == 0 {
                        v___x_3561_ = lean_unsigned_to_nat(1);
                        v___x_3562_ = lean_nat_add(v_i_3555_, v___x_3561_);
                        lean_dec(v_i_3555_);
                        v_i_3555_ = v___x_3562_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_3555_);
                        return v___x_3560_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_keys_3564_: *mut LeanObject,
    mut v_i_3565_: *mut LeanObject,
    mut v_k_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3567_: u8 = 0;
    let mut v_r_3568_: *mut LeanObject = core::ptr::null_mut();
    v_res_3567_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_keys_3564_, v_i_3565_, v_k_3566_);
    lean_dec_ref(v_k_3566_);
    lean_dec_ref(v_keys_3564_);
    v_r_3568_ = lean_box((v_res_3567_) as usize);
    return v_r_3568_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_3569_: *mut LeanObject,
    mut v_x_3570_: usize,
    mut v_x_3571_: *mut LeanObject,
) -> u8 {
    let mut v_es_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: usize = 0;
    let mut v___x_3575_: usize = 0;
    let mut v___x_3576_: usize = 0;
    let mut v_j_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: u8 = 0;
    let mut v_node_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: usize = 0;
    let mut v___x_3584_: u8 = 0;
    let mut v_ks_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3569_) == 0 {
                    v_es_3572_ = lean_ctor_get(v_x_3569_, 0);
                    v___x_3573_ = lean_box(2);
                    v___x_3574_ = 5usize;
                    v___x_3575_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Meta_Sym_Simp_Theorems_insert_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
                    v___x_3576_ = lean_usize_land(v_x_3570_, v___x_3575_);
                    v_j_3577_ = lean_usize_to_nat(v___x_3576_);
                    v___x_3578_ = lean_array_get_borrowed(v___x_3573_, v_es_3572_, v_j_3577_);
                    lean_dec(v_j_3577_);
                    match lean_obj_tag(v___x_3578_) {
                        0 => {
                            v_key_3579_ = lean_ctor_get(v___x_3578_, 0);
                            v___x_3580_ = l_Lean_instBEqExtraModUse_beq(v_x_3571_, v_key_3579_);
                            return v___x_3580_;
                        }
                        1 => {
                            v_node_3581_ = lean_ctor_get(v___x_3578_, 0);
                            v___x_3582_ = lean_usize_shift_right(v_x_3570_, v___x_3574_);
                            v_x_3569_ = v_node_3581_;
                            v_x_3570_ = v___x_3582_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3584_ = 0;
                            return v___x_3584_;
                        }
                    }
                } else {
                    v_ks_3585_ = lean_ctor_get(v_x_3569_, 0);
                    v___x_3586_ = lean_unsigned_to_nat(0);
                    v___x_3587_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ks_3585_, v___x_3586_, v_x_3571_);
                    return v___x_3587_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_x_3588_: *mut LeanObject,
    mut v_x_3589_: *mut LeanObject,
    mut v_x_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3832__boxed_3591_: usize = 0;
    let mut v_res_3592_: u8 = 0;
    let mut v_r_3593_: *mut LeanObject = core::ptr::null_mut();
    v_x_3832__boxed_3591_ = lean_unbox_usize(v_x_3589_);
    lean_dec(v_x_3589_);
    v_res_3592_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4___redArg(v_x_3588_, v_x_3832__boxed_3591_, v_x_3590_);
    lean_dec_ref(v_x_3590_);
    lean_dec_ref(v_x_3588_);
    v_r_3593_ = lean_box((v_res_3592_) as usize);
    return v_r_3593_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3___redArg(
    mut v_x_3594_: *mut LeanObject,
    mut v_x_3595_: *mut LeanObject,
) -> u8 {
    let mut v___x_3596_: u64 = 0;
    let mut v___x_3597_: usize = 0;
    let mut v___x_3598_: u8 = 0;
    v___x_3596_ = l_Lean_instHashableExtraModUse_hash(v_x_3595_);
    v___x_3597_ = lean_uint64_to_usize(v___x_3596_);
    v___x_3598_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4___redArg(v_x_3594_, v___x_3597_, v_x_3595_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_x_3599_: *mut LeanObject,
    mut v_x_3600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3601_: u8 = 0;
    let mut v_r_3602_: *mut LeanObject = core::ptr::null_mut();
    v_res_3601_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3___redArg(v_x_3599_, v_x_3600_);
    lean_dec_ref(v_x_3600_);
    lean_dec_ref(v_x_3599_);
    v_r_3602_ = lean_box((v_res_3601_) as usize);
    return v_r_3602_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__0()
-> *mut LeanObject {
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3603_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1()
-> *mut LeanObject {
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    v___x_3604_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__0);
    v___x_3605_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3605_, 0, v___x_3604_);
    return v___x_3605_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__2()
-> *mut LeanObject {
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    v___x_3606_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1);
    v___x_3607_ = lean_unsigned_to_nat(0);
    v___x_3608_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3608_, 0, v___x_3607_);
    lean_ctor_set(v___x_3608_, 1, v___x_3607_);
    lean_ctor_set(v___x_3608_, 2, v___x_3607_);
    lean_ctor_set(v___x_3608_, 3, v___x_3607_);
    lean_ctor_set(v___x_3608_, 4, v___x_3606_);
    lean_ctor_set(v___x_3608_, 5, v___x_3606_);
    lean_ctor_set(v___x_3608_, 6, v___x_3606_);
    lean_ctor_set(v___x_3608_, 7, v___x_3606_);
    lean_ctor_set(v___x_3608_, 8, v___x_3606_);
    lean_ctor_set(v___x_3608_, 9, v___x_3606_);
    return v___x_3608_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    v___x_3609_ = lean_unsigned_to_nat(32);
    v___x_3610_ = lean_mk_empty_array_with_capacity(v___x_3609_);
    v___x_3611_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3611_, 0, v___x_3610_);
    return v___x_3611_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__4()
-> *mut LeanObject {
    let mut v___x_3612_: usize = 0;
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    v___x_3612_ = 5usize;
    v___x_3613_ = lean_unsigned_to_nat(0);
    v___x_3614_ = lean_unsigned_to_nat(32);
    v___x_3615_ = lean_mk_empty_array_with_capacity(v___x_3614_);
    v___x_3616_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__3);
    v___x_3617_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3617_, 0, v___x_3616_);
    lean_ctor_set(v___x_3617_, 1, v___x_3615_);
    lean_ctor_set(v___x_3617_, 2, v___x_3613_);
    lean_ctor_set(v___x_3617_, 3, v___x_3613_);
    lean_ctor_set_usize(v___x_3617_, 4, v___x_3612_);
    return v___x_3617_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__5()
-> *mut LeanObject {
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    v___x_3618_ = lean_box(1);
    v___x_3619_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__4);
    v___x_3620_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__1);
    v___x_3621_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3621_, 0, v___x_3620_);
    lean_ctor_set(v___x_3621_, 1, v___x_3619_);
    lean_ctor_set(v___x_3621_, 2, v___x_3618_);
    return v___x_3621_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6(
    mut v_msgData_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    v___x_3626_ = lean_st_ref_get(v___y_3624_);
    v_env_3627_ = lean_ctor_get(v___x_3626_, 0);
    lean_inc_ref(v_env_3627_);
    lean_dec(v___x_3626_);
    v_options_3628_ = lean_ctor_get(v___y_3623_, 2);
    v___x_3629_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__2);
    v___x_3630_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___closed__5);
    lean_inc_ref(v_options_3628_);
    v___x_3631_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3631_, 0, v_env_3627_);
    lean_ctor_set(v___x_3631_, 1, v___x_3629_);
    lean_ctor_set(v___x_3631_, 2, v___x_3630_);
    lean_ctor_set(v___x_3631_, 3, v_options_3628_);
    v___x_3632_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3632_, 0, v___x_3631_);
    lean_ctor_set(v___x_3632_, 1, v_msgData_3622_);
    v___x_3633_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3633_, 0, v___x_3632_);
    return v___x_3633_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_msgData_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3638_: *mut LeanObject = core::ptr::null_mut();
    v_res_3638_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6(v_msgData_3634_, v___y_3635_, v___y_3636_);
    lean_dec(v___y_3636_);
    lean_dec_ref(v___y_3635_);
    return v_res_3638_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__0()
-> f64 {
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: f64 = 0.0;
    v___x_3639_ = lean_unsigned_to_nat(0);
    v___x_3640_ = lean_float_of_nat(v___x_3639_);
    return v___x_3640_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4(
    mut v_cls_3644_: *mut LeanObject,
    mut v_msg_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v_tid_3668_: u64 = 0;
    let mut v_traces_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: f64 = 0.0;
    let mut v___x_3675_: u8 = 0;
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3649_ = lean_ctor_get(v___y_3646_, 5);
                v___x_3650_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4_spec__6(v_msg_3645_, v___y_3646_, v___y_3647_);
                v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
                v_isSharedCheck_3695_ = (!lean_is_exclusive(v___x_3650_)) as u8;
                if v_isSharedCheck_3695_ == 0 {
                    v___x_3653_ = v___x_3650_;
                    v_isShared_3654_ = v_isSharedCheck_3695_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3651_);
                    lean_dec(v___x_3650_);
                    v___x_3653_ = lean_box(0);
                    v_isShared_3654_ = v_isSharedCheck_3695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3655_ = lean_st_ref_take(v___y_3647_);
                v_traceState_3656_ = lean_ctor_get(v___x_3655_, 4);
                v_env_3657_ = lean_ctor_get(v___x_3655_, 0);
                v_nextMacroScope_3658_ = lean_ctor_get(v___x_3655_, 1);
                v_ngen_3659_ = lean_ctor_get(v___x_3655_, 2);
                v_auxDeclNGen_3660_ = lean_ctor_get(v___x_3655_, 3);
                v_cache_3661_ = lean_ctor_get(v___x_3655_, 5);
                v_messages_3662_ = lean_ctor_get(v___x_3655_, 6);
                v_infoState_3663_ = lean_ctor_get(v___x_3655_, 7);
                v_snapshotTasks_3664_ = lean_ctor_get(v___x_3655_, 8);
                v_isSharedCheck_3694_ = (!lean_is_exclusive(v___x_3655_)) as u8;
                if v_isSharedCheck_3694_ == 0 {
                    v___x_3666_ = v___x_3655_;
                    v_isShared_3667_ = v_isSharedCheck_3694_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3664_);
                    lean_inc(v_infoState_3663_);
                    lean_inc(v_messages_3662_);
                    lean_inc(v_cache_3661_);
                    lean_inc(v_traceState_3656_);
                    lean_inc(v_auxDeclNGen_3660_);
                    lean_inc(v_ngen_3659_);
                    lean_inc(v_nextMacroScope_3658_);
                    lean_inc(v_env_3657_);
                    lean_dec(v___x_3655_);
                    v___x_3666_ = lean_box(0);
                    v_isShared_3667_ = v_isSharedCheck_3694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3668_ = lean_ctor_get_uint64(
                    v_traceState_3656_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3669_ = lean_ctor_get(v_traceState_3656_, 0);
                v_isSharedCheck_3693_ = (!lean_is_exclusive(v_traceState_3656_)) as u8;
                if v_isSharedCheck_3693_ == 0 {
                    v___x_3671_ = v_traceState_3656_;
                    v_isShared_3672_ = v_isSharedCheck_3693_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3669_);
                    lean_dec(v_traceState_3656_);
                    v___x_3671_ = lean_box(0);
                    v_isShared_3672_ = v_isSharedCheck_3693_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3673_ = lean_box(0);
                v___x_3674_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__0);
                v___x_3675_ = 0;
                v___x_3676_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__1;
                v___x_3677_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3677_, 0, v_cls_3644_);
                lean_ctor_set(v___x_3677_, 1, v___x_3673_);
                lean_ctor_set(v___x_3677_, 2, v___x_3676_);
                lean_ctor_set_float(
                    v___x_3677_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3674_,
                );
                lean_ctor_set_float(
                    v___x_3677_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3674_,
                );
                lean_ctor_set_uint8(
                    v___x_3677_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3675_,
                );
                v___x_3678_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__2;
                v___x_3679_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3679_, 0, v___x_3677_);
                lean_ctor_set(v___x_3679_, 1, v_a_3651_);
                lean_ctor_set(v___x_3679_, 2, v___x_3678_);
                lean_inc(v_ref_3649_);
                v___x_3680_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3680_, 0, v_ref_3649_);
                lean_ctor_set(v___x_3680_, 1, v___x_3679_);
                v___x_3681_ = l_Lean_PersistentArray_push___redArg(v_traces_3669_, v___x_3680_);
                if v_isShared_3672_ == 0 {
                    lean_ctor_set(v___x_3671_, 0, v___x_3681_);
                    v___x_3683_ = v___x_3671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3681_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3692_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3668_,
                    );
                    v___x_3683_ = v_reuseFailAlloc_3692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3667_ == 0 {
                    lean_ctor_set(v___x_3666_, 4, v___x_3683_);
                    v___x_3685_ = v___x_3666_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_env_3657_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_nextMacroScope_3658_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 2, v_ngen_3659_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 3, v_auxDeclNGen_3660_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 4, v___x_3683_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 5, v_cache_3661_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 6, v_messages_3662_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 7, v_infoState_3663_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 8, v_snapshotTasks_3664_);
                    v___x_3685_ = v_reuseFailAlloc_3691_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3686_ = lean_st_ref_set(v___y_3647_, v___x_3685_);
                v___x_3687_ = lean_box(0);
                if v_isShared_3654_ == 0 {
                    lean_ctor_set(v___x_3653_, 0, v___x_3687_);
                    v___x_3689_ = v___x_3653_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___boxed(
    mut v_cls_3696_: *mut LeanObject,
    mut v_msg_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3701_: *mut LeanObject = core::ptr::null_mut();
    v_res_3701_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4(v_cls_3696_, v_msg_3697_, v___y_3698_, v___y_3699_);
    lean_dec(v___y_3699_);
    lean_dec_ref(v___y_3698_);
    return v_res_3701_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    v___x_3704_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__1;
    v___x_3705_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__0;
    v___x_3706_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3705_, v___x_3704_);
    return v___x_3706_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    v___x_3707_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3707_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    v___x_3708_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__3);
    v___x_3709_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3709_, 0, v___x_3708_);
    return v___x_3709_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    v___x_3710_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__4);
    v___x_3711_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3711_, 0, v___x_3710_);
    lean_ctor_set(v___x_3711_, 1, v___x_3710_);
    return v___x_3711_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__9()
-> *mut LeanObject {
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    v___x_3716_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__8;
    v___x_3717_ = l_Lean_stringToMessageData(v___x_3716_);
    return v___x_3717_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__11()
-> *mut LeanObject {
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3719_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__10;
    v___x_3720_ = l_Lean_stringToMessageData(v___x_3719_);
    return v___x_3720_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__12()
-> *mut LeanObject {
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    v___x_3721_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4___closed__1;
    v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
    return v___x_3722_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__15()
-> *mut LeanObject {
    let mut v_cls_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    v_cls_3726_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__7;
    v___x_3727_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__14;
    v___x_3728_ = l_Lean_Name_append(v___x_3727_, v_cls_3726_);
    return v___x_3728_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__17()
-> *mut LeanObject {
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    v___x_3730_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__16;
    v___x_3731_ = l_Lean_stringToMessageData(v___x_3730_);
    return v___x_3731_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__19()
-> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    v___x_3733_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__18;
    v___x_3734_ = l_Lean_stringToMessageData(v___x_3733_);
    return v___x_3734_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2(
    mut v_mod_3739_: *mut LeanObject,
    mut v_isMeta_3740_: u8,
    mut v_hint_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3747_: u8 = 0;
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v_asyncMode_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_unused_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: u8 = 0;
    let mut v_options_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3784_: u8 = 0;
    let mut v_inheritedTraceOptions_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: u8 = 0;
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3745_ = lean_st_ref_get(v___y_3743_);
                v_env_3746_ = lean_ctor_get(v___x_3745_, 0);
                lean_inc_ref(v_env_3746_);
                lean_dec(v___x_3745_);
                v_isExporting_3747_ = lean_ctor_get_uint8(
                    v_env_3746_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_3746_);
                v___x_3748_ = lean_st_ref_get(v___y_3743_);
                v_env_3749_ = lean_ctor_get(v___x_3748_, 0);
                lean_inc_ref(v_env_3749_);
                lean_dec(v___x_3748_);
                v___x_3750_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__2);
                lean_inc(v_mod_3739_);
                v_entry_3751_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_3751_, 0, v_mod_3739_);
                lean_ctor_set_uint8(
                    v_entry_3751_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_3747_,
                );
                lean_ctor_set_uint8(
                    v_entry_3751_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_3740_,
                );
                v___x_3752_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_3753_ = lean_box(1);
                v___x_3754_ = lean_box(0);
                v___x_3781_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3750_,
                    v___x_3752_,
                    v_env_3749_,
                    v___x_3753_,
                    v___x_3754_,
                );
                v___x_3782_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3___redArg(v___x_3781_, v_entry_3751_);
                lean_dec(v___x_3781_);
                if v___x_3782_ == 0 {
                    v_options_3783_ = lean_ctor_get(v___y_3742_, 2);
                    v_hasTrace_3784_ = lean_ctor_get_uint8(
                        v_options_3783_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3784_ == 0 {
                        lean_dec(v_hint_3741_);
                        lean_dec(v_mod_3739_);
                        v___y_3756_ = v___y_3743_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3785_ = lean_ctor_get(v___y_3742_, 13);
                        v_cls_3786_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__7;
                        v___x_3806_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__15_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__15);
                        v___x_3807_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3785_,
                            v_options_3783_,
                            v___x_3806_,
                        );
                        if v___x_3807_ == 0 {
                            lean_dec(v_hint_3741_);
                            lean_dec(v_mod_3739_);
                            v___y_3756_ = v___y_3743_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3808_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__17_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__17);
                            if v_isExporting_3747_ == 0 {
                                v___x_3817_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__22;
                                v___y_3810_ = v___x_3817_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3818_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__23;
                                v___y_3810_ = v___x_3818_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v_entry_3751_, 1);
                    lean_dec(v_hint_3741_);
                    lean_dec(v_mod_3739_);
                    v___x_3819_ = lean_box(0);
                    v___x_3820_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3820_, 0, v___x_3819_);
                    return v___x_3820_;
                }
            }
            1 => {
                v___x_3757_ = lean_st_ref_take(v___y_3756_);
                v_toEnvExtension_3758_ = lean_ctor_get(v___x_3752_, 0);
                v_env_3759_ = lean_ctor_get(v___x_3757_, 0);
                v_nextMacroScope_3760_ = lean_ctor_get(v___x_3757_, 1);
                v_ngen_3761_ = lean_ctor_get(v___x_3757_, 2);
                v_auxDeclNGen_3762_ = lean_ctor_get(v___x_3757_, 3);
                v_traceState_3763_ = lean_ctor_get(v___x_3757_, 4);
                v_messages_3764_ = lean_ctor_get(v___x_3757_, 6);
                v_infoState_3765_ = lean_ctor_get(v___x_3757_, 7);
                v_snapshotTasks_3766_ = lean_ctor_get(v___x_3757_, 8);
                v_isSharedCheck_3779_ = (!lean_is_exclusive(v___x_3757_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v_unused_3780_ = lean_ctor_get(v___x_3757_, 5);
                    lean_dec(v_unused_3780_);
                    v___x_3768_ = v___x_3757_;
                    v_isShared_3769_ = v_isSharedCheck_3779_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3766_);
                    lean_inc(v_infoState_3765_);
                    lean_inc(v_messages_3764_);
                    lean_inc(v_traceState_3763_);
                    lean_inc(v_auxDeclNGen_3762_);
                    lean_inc(v_ngen_3761_);
                    lean_inc(v_nextMacroScope_3760_);
                    lean_inc(v_env_3759_);
                    lean_dec(v___x_3757_);
                    v___x_3768_ = lean_box(0);
                    v_isShared_3769_ = v_isSharedCheck_3779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_3770_ = lean_ctor_get(v_toEnvExtension_3758_, 2);
                v___x_3771_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3752_,
                    v_env_3759_,
                    v_entry_3751_,
                    v_asyncMode_3770_,
                    v___x_3754_,
                );
                v___x_3772_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__5);
                if v_isShared_3769_ == 0 {
                    lean_ctor_set(v___x_3768_, 5, v___x_3772_);
                    lean_ctor_set(v___x_3768_, 0, v___x_3771_);
                    v___x_3774_ = v___x_3768_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3771_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_nextMacroScope_3760_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_ngen_3761_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_auxDeclNGen_3762_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_traceState_3763_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 5, v___x_3772_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_messages_3764_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_infoState_3765_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_snapshotTasks_3766_);
                    v___x_3774_ = v_reuseFailAlloc_3778_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3775_ = lean_st_ref_set(v___y_3756_, v___x_3774_);
                v___x_3776_ = lean_box(0);
                v___x_3777_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3777_, 0, v___x_3776_);
                return v___x_3777_;
            }
            4 => {
                v___x_3790_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3790_, 0, v___y_3788_);
                lean_ctor_set(v___x_3790_, 1, v___y_3789_);
                v___x_3791_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__4(v_cls_3786_, v___x_3790_, v___y_3742_, v___y_3743_);
                if lean_obj_tag(v___x_3791_) == 0 {
                    lean_dec_ref_known(v___x_3791_, 1);
                    v___y_3756_ = v___y_3743_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_3751_, 1);
                    return v___x_3791_;
                }
            }
            5 => {
                lean_inc_ref(v___y_3794_);
                v___x_3795_ = l_Lean_stringToMessageData(v___y_3794_);
                v___x_3796_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3796_, 0, v___y_3793_);
                lean_ctor_set(v___x_3796_, 1, v___x_3795_);
                v___x_3797_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__9);
                v___x_3798_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3798_, 0, v___x_3796_);
                lean_ctor_set(v___x_3798_, 1, v___x_3797_);
                v___x_3799_ = l_Lean_MessageData_ofName(v_mod_3739_);
                v___x_3800_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3800_, 0, v___x_3798_);
                lean_ctor_set(v___x_3800_, 1, v___x_3799_);
                v___x_3801_ = l_Lean_Name_isAnonymous(v_hint_3741_);
                if v___x_3801_ == 0 {
                    v___x_3802_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__11), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__11_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__11);
                    v___x_3803_ = l_Lean_MessageData_ofName(v_hint_3741_);
                    v___x_3804_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3804_, 0, v___x_3802_);
                    lean_ctor_set(v___x_3804_, 1, v___x_3803_);
                    v___y_3788_ = v___x_3800_;
                    v___y_3789_ = v___x_3804_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_3741_);
                    v___x_3805_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__12);
                    v___y_3788_ = v___x_3800_;
                    v___y_3789_ = v___x_3805_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_3810_);
                v___x_3811_ = l_Lean_stringToMessageData(v___y_3810_);
                v___x_3812_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3812_, 0, v___x_3808_);
                lean_ctor_set(v___x_3812_, 1, v___x_3811_);
                v___x_3813_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__19_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__19);
                v___x_3814_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3814_, 0, v___x_3812_);
                lean_ctor_set(v___x_3814_, 1, v___x_3813_);
                if v_isMeta_3740_ == 0 {
                    v___x_3815_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__20;
                    v___y_3793_ = v___x_3814_;
                    v___y_3794_ = v___x_3815_;
                    state = 5;
                    continue;
                } else {
                    v___x_3816_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___closed__21;
                    v___y_3793_ = v___x_3814_;
                    v___y_3794_ = v___x_3816_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2___boxed(
    mut v_mod_3821_: *mut LeanObject,
    mut v_isMeta_3822_: *mut LeanObject,
    mut v_hint_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3827_: u8 = 0;
    let mut v_res_3828_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3827_ = (lean_unbox(v_isMeta_3822_) as u8);
    v_res_3828_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2(v_mod_3821_, v_isMeta_boxed_3827_, v_hint_3823_, v___y_3824_, v___y_3825_);
    lean_dec(v___y_3825_);
    lean_dec_ref(v___y_3824_);
    return v_res_3828_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0___redArg(
    mut v_a_3829_: *mut LeanObject,
    mut v_x_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: u8 = 0;
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3830_) == 0 {
                    v___x_3831_ = lean_box(0);
                    return v___x_3831_;
                } else {
                    v_key_3832_ = lean_ctor_get(v_x_3830_, 0);
                    v_value_3833_ = lean_ctor_get(v_x_3830_, 1);
                    v_tail_3834_ = lean_ctor_get(v_x_3830_, 2);
                    v___x_3835_ = lean_name_eq(v_key_3832_, v_a_3829_);
                    if v___x_3835_ == 0 {
                        v_x_3830_ = v_tail_3834_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3833_);
                        v___x_3837_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3837_, 0, v_value_3833_);
                        return v___x_3837_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_3838_: *mut LeanObject,
    mut v_x_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3840_: *mut LeanObject = core::ptr::null_mut();
    v_res_3840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0___redArg(v_a_3838_, v_x_3839_);
    lean_dec(v_x_3839_);
    lean_dec(v_a_3838_);
    return v_res_3840_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u64 = 0;
    v___x_3841_ = lean_unsigned_to_nat(1723);
    v___x_3842_ = lean_uint64_of_nat(v___x_3841_);
    return v___x_3842_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg(
    mut v_m_3843_: *mut LeanObject,
    mut v_a_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: u64 = 0;
    let mut v___x_3849_: u64 = 0;
    let mut v___x_3850_: u64 = 0;
    let mut v_fold_3851_: u64 = 0;
    let mut v___x_3852_: u64 = 0;
    let mut v___x_3853_: u64 = 0;
    let mut v___x_3854_: u64 = 0;
    let mut v___x_3855_: usize = 0;
    let mut v___x_3856_: usize = 0;
    let mut v___x_3857_: usize = 0;
    let mut v___x_3858_: usize = 0;
    let mut v___x_3859_: usize = 0;
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u64 = 0;
    let mut v_hash_3863_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3845_ = lean_ctor_get(v_m_3843_, 1);
                v___x_3846_ = lean_array_get_size(v_buckets_3845_);
                if lean_obj_tag(v_a_3844_) == 0 {
                    v___x_3862_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg___closed__0);
                    v___y_3848_ = v___x_3862_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3863_ = lean_ctor_get_uint64(
                        v_a_3844_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3848_ = v_hash_3863_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3849_ = 32u64;
                v___x_3850_ = lean_uint64_shift_right(v___y_3848_, v___x_3849_);
                v_fold_3851_ = lean_uint64_xor(v___y_3848_, v___x_3850_);
                v___x_3852_ = 16u64;
                v___x_3853_ = lean_uint64_shift_right(v_fold_3851_, v___x_3852_);
                v___x_3854_ = lean_uint64_xor(v_fold_3851_, v___x_3853_);
                v___x_3855_ = lean_uint64_to_usize(v___x_3854_);
                v___x_3856_ = lean_usize_of_nat(v___x_3846_);
                v___x_3857_ = 1usize;
                v___x_3858_ = lean_usize_sub(v___x_3856_, v___x_3857_);
                v___x_3859_ = lean_usize_land(v___x_3855_, v___x_3858_);
                v___x_3860_ = lean_array_uget_borrowed(v_buckets_3845_, v___x_3859_);
                v___x_3861_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0___redArg(v_a_3844_, v___x_3860_);
                return v___x_3861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg___boxed(
    mut v_m_3864_: *mut LeanObject,
    mut v_a_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3866_: *mut LeanObject = core::ptr::null_mut();
    v_res_3866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg(v_m_3864_, v_a_3865_);
    lean_dec(v_a_3865_);
    lean_dec_ref(v_m_3864_);
    return v_res_3866_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__3(
    mut v___x_3867_: *mut LeanObject,
    mut v_declName_3868_: *mut LeanObject,
    mut v_as_3869_: *mut LeanObject,
    mut v_sz_3870_: usize,
    mut v_i_3871_: usize,
    mut v_b_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3876_: u8 = 0;
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: usize = 0;
    let mut v___x_3889_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3876_ = lean_usize_dec_lt(v_i_3871_, v_sz_3870_);
                if v___x_3876_ == 0 {
                    lean_dec(v_declName_3868_);
                    v___x_3877_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3877_, 0, v_b_3872_);
                    return v___x_3877_;
                } else {
                    v___x_3878_ = l_Lean_Environment_header(v___x_3867_);
                    v_modules_3879_ = lean_ctor_get(v___x_3878_, 3);
                    lean_inc_ref(v_modules_3879_);
                    lean_dec_ref(v___x_3878_);
                    v___x_3880_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_3881_ = lean_array_uget_borrowed(v_as_3869_, v_i_3871_);
                    v___x_3882_ = lean_array_get(v___x_3880_, v_modules_3879_, v_a_3881_);
                    lean_dec_ref(v_modules_3879_);
                    v_toImport_3883_ = lean_ctor_get(v___x_3882_, 0);
                    lean_inc_ref(v_toImport_3883_);
                    lean_dec(v___x_3882_);
                    v_module_3884_ = lean_ctor_get(v_toImport_3883_, 0);
                    lean_inc(v_module_3884_);
                    lean_dec_ref(v_toImport_3883_);
                    v___x_3885_ = 0;
                    lean_inc(v_declName_3868_);
                    v___x_3886_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2(v_module_3884_, v___x_3885_, v_declName_3868_, v___y_3873_, v___y_3874_);
                    if lean_obj_tag(v___x_3886_) == 0 {
                        lean_dec_ref_known(v___x_3886_, 1);
                        v___x_3887_ = lean_box(0);
                        v___x_3888_ = 1usize;
                        v___x_3889_ = lean_usize_add(v_i_3871_, v___x_3888_);
                        v_i_3871_ = v___x_3889_;
                        v_b_3872_ = v___x_3887_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_3868_);
                        return v___x_3886_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__3___boxed(
    mut v___x_3891_: *mut LeanObject,
    mut v_declName_3892_: *mut LeanObject,
    mut v_as_3893_: *mut LeanObject,
    mut v_sz_3894_: *mut LeanObject,
    mut v_i_3895_: *mut LeanObject,
    mut v_b_3896_: *mut LeanObject,
    mut v___y_3897_: *mut LeanObject,
    mut v___y_3898_: *mut LeanObject,
    mut v___y_3899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3900_: usize = 0;
    let mut v_i_boxed_3901_: usize = 0;
    let mut v_res_3902_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3900_ = lean_unbox_usize(v_sz_3894_);
    lean_dec(v_sz_3894_);
    v_i_boxed_3901_ = lean_unbox_usize(v_i_3895_);
    lean_dec(v_i_3895_);
    v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__3(v___x_3891_, v_declName_3892_, v_as_3893_, v_sz_boxed_3900_, v_i_boxed_3901_, v_b_3896_, v___y_3897_, v___y_3898_);
    lean_dec(v___y_3898_);
    lean_dec_ref(v___y_3897_);
    lean_dec_ref(v_as_3893_);
    lean_dec_ref(v___x_3891_);
    return v_res_3902_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    v___x_3905_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__1;
    v___x_3906_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__0;
    v___x_3907_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3906_, v___x_3905_);
    return v___x_3907_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1(
    mut v_declName_3910_: *mut LeanObject,
    mut v_isMeta_3911_: u8,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3923_: usize = 0;
    let mut v___x_3924_: usize = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut v_unused_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: u8 = 0;
    let mut v_toImport_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v___x_3957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3915_ = lean_st_ref_get(v___y_3913_);
                v_env_3919_ = lean_ctor_get(v___x_3915_, 0);
                lean_inc_ref(v_env_3919_);
                lean_dec(v___x_3915_);
                v___x_3934_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3919_, v_declName_3910_);
                if lean_obj_tag(v___x_3934_) == 0 {
                    lean_dec_ref(v_env_3919_);
                    lean_dec(v_declName_3910_);
                    state = 1;
                    continue;
                } else {
                    v_val_3935_ = lean_ctor_get(v___x_3934_, 0);
                    lean_inc(v_val_3935_);
                    lean_dec_ref_known(v___x_3934_, 1);
                    v___x_3936_ = l_Lean_Environment_header(v_env_3919_);
                    v_modules_3937_ = lean_ctor_get(v___x_3936_, 3);
                    lean_inc_ref(v_modules_3937_);
                    lean_dec_ref(v___x_3936_);
                    v___x_3938_ = lean_array_get_size(v_modules_3937_);
                    v___x_3939_ = lean_nat_dec_lt(v_val_3935_, v___x_3938_);
                    if v___x_3939_ == 0 {
                        lean_dec_ref(v_modules_3937_);
                        lean_dec(v_val_3935_);
                        lean_dec_ref(v_env_3919_);
                        lean_dec(v_declName_3910_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3940_ = lean_st_ref_get(v___y_3913_);
                        v_env_3941_ = lean_ctor_get(v___x_3940_, 0);
                        lean_inc_ref(v_env_3941_);
                        lean_dec(v___x_3940_);
                        v___x_3942_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__2);
                        v___x_3943_ = lean_array_fget(v_modules_3937_, v_val_3935_);
                        lean_dec(v_val_3935_);
                        lean_dec_ref(v_modules_3937_);
                        if v_isMeta_3911_ == 0 {
                            lean_dec_ref(v_env_3941_);
                            v___y_3945_ = v_isMeta_3911_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_3910_);
                            v___x_3956_ = l_Lean_isMarkedMeta(v_env_3941_, v_declName_3910_);
                            if v___x_3956_ == 0 {
                                v___y_3945_ = v_isMeta_3911_;
                                state = 5;
                                continue;
                            } else {
                                v___x_3957_ = 0;
                                v___y_3945_ = v___x_3957_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3917_ = lean_box(0);
                v___x_3918_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3918_, 0, v___x_3917_);
                return v___x_3918_;
            }
            2 => {
                v___x_3922_ = lean_box(0);
                v_sz_3923_ = lean_array_size(v___y_3921_);
                v___x_3924_ = 0usize;
                v___x_3925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__3(v_env_3919_, v_declName_3910_, v___y_3921_, v_sz_3923_, v___x_3924_, v___x_3922_, v___y_3912_, v___y_3913_);
                lean_dec_ref(v___y_3921_);
                lean_dec_ref(v_env_3919_);
                if lean_obj_tag(v___x_3925_) == 0 {
                    v_isSharedCheck_3932_ = (!lean_is_exclusive(v___x_3925_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v_unused_3933_ = lean_ctor_get(v___x_3925_, 0);
                        lean_dec(v_unused_3933_);
                        v___x_3927_ = v___x_3925_;
                        v_isShared_3928_ = v_isSharedCheck_3932_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_3925_);
                        v___x_3927_ = lean_box(0);
                        v_isShared_3928_ = v_isSharedCheck_3932_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_3925_;
                }
            }
            3 => {
                if v_isShared_3928_ == 0 {
                    lean_ctor_set(v___x_3927_, 0, v___x_3922_);
                    v___x_3930_ = v___x_3927_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3922_);
                    v___x_3930_ = v_reuseFailAlloc_3931_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3930_;
            }
            5 => {
                v_toImport_3946_ = lean_ctor_get(v___x_3943_, 0);
                lean_inc_ref(v_toImport_3946_);
                lean_dec(v___x_3943_);
                v_module_3947_ = lean_ctor_get(v_toImport_3946_, 0);
                lean_inc(v_module_3947_);
                lean_dec_ref(v_toImport_3946_);
                lean_inc(v_declName_3910_);
                v___x_3948_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2(v_module_3947_, v___y_3945_, v_declName_3910_, v___y_3912_, v___y_3913_);
                if lean_obj_tag(v___x_3948_) == 0 {
                    lean_dec_ref_known(v___x_3948_, 1);
                    v___x_3949_ = l_Lean_indirectModUseExt;
                    v___x_3950_ = lean_box(1);
                    v___x_3951_ = lean_box(0);
                    lean_inc_ref(v_env_3919_);
                    v___x_3952_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_3942_,
                        v___x_3949_,
                        v_env_3919_,
                        v___x_3950_,
                        v___x_3951_,
                    );
                    v___x_3953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg(v___x_3952_, v_declName_3910_);
                    lean_dec(v___x_3952_);
                    if lean_obj_tag(v___x_3953_) == 0 {
                        v___x_3954_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___closed__3;
                        v___y_3921_ = v___x_3954_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3955_ = lean_ctor_get(v___x_3953_, 0);
                        lean_inc(v_val_3955_);
                        lean_dec_ref_known(v___x_3953_, 1);
                        v___y_3921_ = v_val_3955_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_3919_);
                    lean_dec(v_declName_3910_);
                    return v___x_3948_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1___boxed(
    mut v_declName_3958_: *mut LeanObject,
    mut v_isMeta_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3963_: u8 = 0;
    let mut v_res_3964_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3963_ = (lean_unbox(v_isMeta_3959_) as u8);
    v_res_3964_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1(v_declName_3958_, v_isMeta_boxed_3963_, v___y_3960_, v___y_3961_);
    lean_dec(v___y_3961_);
    lean_dec_ref(v___y_3960_);
    return v_res_3964_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpExtension_x3f(
    mut v_attrName_3965_: *mut LeanObject,
    mut v_a_3966_: *mut LeanObject,
    mut v_a_3967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3983_: u8 = 0;
    let mut v_unused_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3988_: u8 = 0;
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3992_: u8 = 0;
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3969_ = l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef;
                v___x_3970_ = lean_st_ref_get(v___x_3969_);
                v___x_3971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg(v___x_3970_, v_attrName_3965_);
                lean_dec(v___x_3970_);
                if lean_obj_tag(v___x_3971_) == 1 {
                    v_val_3972_ = lean_ctor_get(v___x_3971_, 0);
                    lean_inc(v_val_3972_);
                    v_ext_3973_ = lean_ctor_get(v_val_3972_, 1);
                    lean_inc_ref(v_ext_3973_);
                    lean_dec(v_val_3972_);
                    v_name_3974_ = lean_ctor_get(v_ext_3973_, 1);
                    lean_inc(v_name_3974_);
                    lean_dec_ref(v_ext_3973_);
                    v___x_3975_ = 1;
                    v___x_3976_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1(v_name_3974_, v___x_3975_, v_a_3966_, v_a_3967_);
                    if lean_obj_tag(v___x_3976_) == 0 {
                        v_isSharedCheck_3983_ = (!lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_3983_ == 0 {
                            v_unused_3984_ = lean_ctor_get(v___x_3976_, 0);
                            lean_dec(v_unused_3984_);
                            v___x_3978_ = v___x_3976_;
                            v_isShared_3979_ = v_isSharedCheck_3983_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3976_);
                            v___x_3978_ = lean_box(0);
                            v_isShared_3979_ = v_isSharedCheck_3983_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_3971_, 1);
                        v_a_3985_ = lean_ctor_get(v___x_3976_, 0);
                        v_isSharedCheck_3992_ = (!lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_3992_ == 0 {
                            v___x_3987_ = v___x_3976_;
                            v_isShared_3988_ = v_isSharedCheck_3992_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3985_);
                            lean_dec(v___x_3976_);
                            v___x_3987_ = lean_box(0);
                            v_isShared_3988_ = v_isSharedCheck_3992_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3993_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3993_, 0, v___x_3971_);
                    return v___x_3993_;
                }
            }
            1 => {
                if v_isShared_3979_ == 0 {
                    lean_ctor_set(v___x_3978_, 0, v___x_3971_);
                    v___x_3981_ = v___x_3978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3971_);
                    v___x_3981_ = v_reuseFailAlloc_3982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3981_;
            }
            3 => {
                if v_isShared_3988_ == 0 {
                    v___x_3990_ = v___x_3987_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
                    v___x_3990_ = v_reuseFailAlloc_3991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getSymSimpExtension_x3f___boxed(
    mut v_attrName_3994_: *mut LeanObject,
    mut v_a_3995_: *mut LeanObject,
    mut v_a_3996_: *mut LeanObject,
    mut v_a_3997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3998_: *mut LeanObject = core::ptr::null_mut();
    v_res_3998_ =
        l_Lean_Meta_Sym_Simp_getSymSimpExtension_x3f(v_attrName_3994_, v_a_3995_, v_a_3996_);
    lean_dec(v_a_3996_);
    lean_dec_ref(v_a_3995_);
    lean_dec(v_attrName_3994_);
    return v_res_3998_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0(
    mut v_00_u03b2_3999_: *mut LeanObject,
    mut v_m_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    v___x_4002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___redArg(v_m_4000_, v_a_4001_);
    return v___x_4002_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0___boxed(
    mut v_00_u03b2_4003_: *mut LeanObject,
    mut v_m_4004_: *mut LeanObject,
    mut v_a_4005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4006_: *mut LeanObject = core::ptr::null_mut();
    v_res_4006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0(v_00_u03b2_4003_, v_m_4004_, v_a_4005_);
    lean_dec(v_a_4005_);
    lean_dec_ref(v_m_4004_);
    return v_res_4006_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0(
    mut v_00_u03b2_4007_: *mut LeanObject,
    mut v_a_4008_: *mut LeanObject,
    mut v_x_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    v___x_4010_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0___redArg(v_a_4008_, v_x_4009_);
    return v___x_4010_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4011_: *mut LeanObject,
    mut v_a_4012_: *mut LeanObject,
    mut v_x_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4014_: *mut LeanObject = core::ptr::null_mut();
    v_res_4014_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__0_spec__0(v_00_u03b2_4011_, v_a_4012_, v_x_4013_);
    lean_dec(v_x_4013_);
    lean_dec(v_a_4012_);
    return v_res_4014_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4015_: *mut LeanObject,
    mut v_x_4016_: *mut LeanObject,
    mut v_x_4017_: *mut LeanObject,
) -> u8 {
    let mut v___x_4018_: u8 = 0;
    v___x_4018_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3___redArg(v_x_4016_, v_x_4017_);
    return v___x_4018_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_4019_: *mut LeanObject,
    mut v_x_4020_: *mut LeanObject,
    mut v_x_4021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4022_: u8 = 0;
    let mut v_r_4023_: *mut LeanObject = core::ptr::null_mut();
    v_res_4022_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3(v_00_u03b2_4019_, v_x_4020_, v_x_4021_);
    lean_dec_ref(v_x_4021_);
    lean_dec_ref(v_x_4020_);
    v_r_4023_ = lean_box((v_res_4022_) as usize);
    return v_r_4023_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_4024_: *mut LeanObject,
    mut v_x_4025_: *mut LeanObject,
    mut v_x_4026_: usize,
    mut v_x_4027_: *mut LeanObject,
) -> u8 {
    let mut v___x_4028_: u8 = 0;
    v___x_4028_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4___redArg(v_x_4025_, v_x_4026_, v_x_4027_);
    return v___x_4028_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_4029_: *mut LeanObject,
    mut v_x_4030_: *mut LeanObject,
    mut v_x_4031_: *mut LeanObject,
    mut v_x_4032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4588__boxed_4033_: usize = 0;
    let mut v_res_4034_: u8 = 0;
    let mut v_r_4035_: *mut LeanObject = core::ptr::null_mut();
    v_x_4588__boxed_4033_ = lean_unbox_usize(v_x_4031_);
    lean_dec(v_x_4031_);
    v_res_4034_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4029_, v_x_4030_, v_x_4588__boxed_4033_, v_x_4032_);
    lean_dec_ref(v_x_4032_);
    lean_dec_ref(v_x_4030_);
    v_r_4035_ = lean_box((v_res_4034_) as usize);
    return v_r_4035_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_4036_: *mut LeanObject,
    mut v_keys_4037_: *mut LeanObject,
    mut v_vals_4038_: *mut LeanObject,
    mut v_heq_4039_: *mut LeanObject,
    mut v_i_4040_: *mut LeanObject,
    mut v_k_4041_: *mut LeanObject,
) -> u8 {
    let mut v___x_4042_: u8 = 0;
    v___x_4042_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_keys_4037_, v_i_4040_, v_k_4041_);
    return v___x_4042_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_4043_: *mut LeanObject,
    mut v_keys_4044_: *mut LeanObject,
    mut v_vals_4045_: *mut LeanObject,
    mut v_heq_4046_: *mut LeanObject,
    mut v_i_4047_: *mut LeanObject,
    mut v_k_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4049_: u8 = 0;
    let mut v_r_4050_: *mut LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Sym_Simp_getSymSimpExtension_x3f_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_4043_, v_keys_4044_, v_vals_4045_, v_heq_4046_, v_i_4047_, v_k_4048_);
    lean_dec_ref(v_k_4048_);
    lean_dec_ref(v_vals_4045_);
    lean_dec_ref(v_keys_4044_);
    v_r_4050_ = lean_box((v_res_4049_) as usize);
    return v_r_4050_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default =
        _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default();
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default);
    l_Lean_Meta_Sym_Simp_instInhabitedTheorem = _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorem();
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedTheorem);
    l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default =
        _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default();
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedTheorems_default);
    l_Lean_Meta_Sym_Simp_instInhabitedTheorems = _init_l_Lean_Meta_Sym_Simp_instInhabitedTheorems();
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedTheorems);
    res = l___private_Lean_Meta_Sym_Simp_Theorems_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Theorems_3071968463____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Theorems(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1 =
        _init_l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1();
    lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkSymSimpExt___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Theorems(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
}

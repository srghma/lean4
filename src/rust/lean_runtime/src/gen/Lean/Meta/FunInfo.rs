// Lean compiler output
// Module: Lean.Meta.FunInfo
// Imports: Lean.Meta.InferType Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::List::Basic::l_List_any___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_firstFrontendMacroScope,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::System::Promise::l_IO_Promise_result_x21___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Class::l_Lean_getOutParamPositions_x3f;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_getMaxHeartbeats, l_Lean_Core_logSnapshotTask___redArg,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Environment::l_Lean_Environment_areRealizationsEnabledForConst;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_BinderInfo_isExplicit,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasFVar, l_Lean_Expr_hash,
    l_Lean_Expr_isAppOf, l_Lean_Expr_isFVar, l_Lean_Expr_isForall, l_Lean_Expr_sort___override,
    l_Lean_FVarIdSet_insert,
};
use crate::r#gen::Lean::Language::Basic::l_Lean_Language_SnapshotTask_finished___redArg;
use crate::r#gen::Lean::Level::{
    l_Lean_Level_hasMVar, l_Lean_Level_hasMVar___boxed, l_Lean_Level_hash,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_binderInfo, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_,
    l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed,
    l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_getFVarLocalDecl___redArg, l_Lean_Meta_instBEqInfoCacheKey_beq,
    l_Lean_Meta_instBEqInfoCacheKey_beq___boxed,
    l_Lean_Meta_instHashableInfoCacheKey___private__1___boxed,
    l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_isClass_x3f,
    l_Lean_Meta_mkInfoCacheKey___redArg, l_Lean_Meta_realizeValue___redArg,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, l_Lean_Meta_isProp, runtime_initialize_Lean_Meta_InferType,
};
use crate::r#gen::Lean::Meta::TransparencyMode::l_Lean_Meta_TransparencyMode_lt;
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_set_heartbeats,
};
use crate::lean_imports_rs::Init::System::Promise::{lean_io_promise_new, lean_io_promise_resolve};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_apply_5, lean_apply_7, lean_box, lean_box_uint64, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0: u64 = 0;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__0_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__1_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__3_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [70, 117, 110, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__5_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__6_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,15669725307426255984 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__7_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,16779825879972418377 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__8_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__2_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,9730592448070811788 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__9_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__4_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,6201651283846819248 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [70, 117, 110, 73, 110, 102, 111, 69, 110, 118, 67, 97, 99, 104, 101, 75, 101, 121, 0]};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__10_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__11_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject,16320153137974874701 as *mut LeanObject] };
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_instTypeNameFunInfoEnvCacheKey: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl___closed__12_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63__value) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0_value:
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
    m_fun: l_Lean_Meta_instBEqInfoCacheKey_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1_value:
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
    m_fun: l_Lean_Meta_instHashableInfoCacheKey___private__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2_value:
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
    m_fun: l_Lean_Level_hasMVar___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0_value)
        as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__0_value) as *mut LeanObject,4342836574150310743 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 70, 117, 110, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 70, 117, 110, 73, 110, 102, 111, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 103, 101, 116, 70, 117, 110, 73, 110, 102, 111, 65, 117, 120, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 114, 101, 97, 108, 105, 122, 101, 32, 96, 0]};
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [96, 32, 118, 97, 108, 117, 101, 32, 98, 117, 116, 32, 96, 101, 110, 97, 98, 108, 101, 82, 101, 97, 108, 105, 122, 97, 116, 105, 111, 110, 115, 70, 111, 114, 67, 111, 110, 115, 116, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 99, 97, 108, 108, 101, 100, 32, 102, 111, 114, 32, 39, 0]};
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1_value) as *mut LeanObject;
pub static l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [39, 32, 102, 105, 114, 115, 116, 0]};
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2_value) as *mut LeanObject;
pub static l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3_value: LeanStringObject<60> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [69, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 46, 114, 101, 97, 108, 105, 122, 101, 67, 111, 110, 115, 116, 58, 32, 96, 114, 101, 97, 108, 105, 122, 101, 100, 73, 109, 112, 111, 114, 116, 101, 100, 67, 111, 110, 115, 116, 115, 96, 32, 105, 115, 32, 101, 109, 112, 116, 121, 0]};
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3_value) as *mut LeanObject;
pub static l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 18 }, m_objs: [core::ptr::addr_of!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__3_value) as *mut LeanObject] };
static mut l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 114, 101, 97, 108, 105, 122, 101, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(
    mut v_x_2372_: *mut LeanObject,
    mut v_x_2373_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2372_) == 0 {
        if lean_obj_tag(v_x_2373_) == 0 {
            let mut v___x_2374_: u8 = 0;
            v___x_2374_ = 1;
            return v___x_2374_;
        } else {
            let mut v___x_2375_: u8 = 0;
            v___x_2375_ = 0;
            return v___x_2375_;
        }
    } else {
        if lean_obj_tag(v_x_2373_) == 0 {
            let mut v___x_2376_: u8 = 0;
            v___x_2376_ = 0;
            return v___x_2376_;
        } else {
            let mut v_val_2377_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2379_: u8 = 0;
            v_val_2377_ = lean_ctor_get(v_x_2372_, 0);
            v_val_2378_ = lean_ctor_get(v_x_2373_, 0);
            v___x_2379_ = lean_nat_dec_eq(v_val_2377_, v_val_2378_);
            return v___x_2379_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1___boxed(
    mut v_x_2380_: *mut LeanObject,
    mut v_x_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2382_: u8 = 0;
    let mut v_r_2383_: *mut LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_x_2380_, v_x_2381_);
    lean_dec(v_x_2381_);
    lean_dec(v_x_2380_);
    v_r_2383_ = lean_box((v_res_2382_) as usize);
    return v_r_2383_;
}
pub unsafe fn l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(
    mut v_x_2384_: *mut LeanObject,
    mut v_x_2385_: *mut LeanObject,
) -> u8 {
    let mut v___x_2386_: u8 = 0;
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: u8 = 0;
    let mut v_head_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2384_) == 0 {
                    if lean_obj_tag(v_x_2385_) == 0 {
                        v___x_2386_ = 1;
                        return v___x_2386_;
                    } else {
                        v___x_2387_ = 0;
                        return v___x_2387_;
                    }
                } else {
                    if lean_obj_tag(v_x_2385_) == 0 {
                        v___x_2388_ = 0;
                        return v___x_2388_;
                    } else {
                        v_head_2389_ = lean_ctor_get(v_x_2384_, 0);
                        v_tail_2390_ = lean_ctor_get(v_x_2384_, 1);
                        v_head_2391_ = lean_ctor_get(v_x_2385_, 0);
                        v_tail_2392_ = lean_ctor_get(v_x_2385_, 1);
                        v___x_2393_ = lean_level_eq(v_head_2389_, v_head_2391_);
                        if v___x_2393_ == 0 {
                            return v___x_2393_;
                        } else {
                            v_x_2384_ = v_tail_2390_;
                            v_x_2385_ = v_tail_2392_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0___boxed(
    mut v_x_2395_: *mut LeanObject,
    mut v_x_2396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2397_: u8 = 0;
    let mut v_r_2398_: *mut LeanObject = core::ptr::null_mut();
    v_res_2397_ = l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(v_x_2395_, v_x_2396_);
    lean_dec(v_x_2396_);
    lean_dec(v_x_2395_);
    v_r_2398_ = lean_box((v_res_2397_) as usize);
    return v_r_2398_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(
    mut v_x_2399_: *mut LeanObject,
    mut v_x_2400_: *mut LeanObject,
) -> u8 {
    let mut v_c_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ls_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxArgs_x3f_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ls_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxArgs_x3f_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    v_c_2401_ = lean_ctor_get(v_x_2399_, 0);
    v_ls_2402_ = lean_ctor_get(v_x_2399_, 1);
    v_maxArgs_x3f_2403_ = lean_ctor_get(v_x_2399_, 2);
    v_c_2404_ = lean_ctor_get(v_x_2400_, 0);
    v_ls_2405_ = lean_ctor_get(v_x_2400_, 1);
    v_maxArgs_x3f_2406_ = lean_ctor_get(v_x_2400_, 2);
    v___x_2407_ = lean_name_eq(v_c_2401_, v_c_2404_);
    if v___x_2407_ == 0 {
        return v___x_2407_;
    } else {
        let mut v___x_2408_: u8 = 0;
        v___x_2408_ = l_List_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__0(v_ls_2402_, v_ls_2405_);
        if v___x_2408_ == 0 {
            return v___x_2408_;
        } else {
            let mut v___x_2409_: u8 = 0;
            v___x_2409_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq_spec__1(v_maxArgs_x3f_2403_, v_maxArgs_x3f_2406_);
            return v___x_2409_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq___boxed(
    mut v_x_2410_: *mut LeanObject,
    mut v_x_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2412_: u8 = 0;
    let mut v_r_2413_: *mut LeanObject = core::ptr::null_mut();
    v_res_2412_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(
        v_x_2410_, v_x_2411_,
    );
    lean_dec_ref(v_x_2411_);
    lean_dec_ref(v_x_2410_);
    v_r_2413_ = lean_box((v_res_2412_) as usize);
    return v_r_2413_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(
    mut v_x_2416_: u64,
    mut v_x_2417_: *mut LeanObject,
) -> u64 {
    let mut v_head_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u64 = 0;
    let mut v___x_2421_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2417_) == 0 {
                    return v_x_2416_;
                } else {
                    v_head_2418_ = lean_ctor_get(v_x_2417_, 0);
                    v_tail_2419_ = lean_ctor_get(v_x_2417_, 1);
                    v___x_2420_ = l_Lean_Level_hash(v_head_2418_);
                    v___x_2421_ = lean_uint64_mix_hash(v_x_2416_, v___x_2420_);
                    v_x_2416_ = v___x_2421_;
                    v_x_2417_ = v_tail_2419_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0___boxed(
    mut v_x_2423_: *mut LeanObject,
    mut v_x_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_109__boxed_2425_: u64 = 0;
    let mut v_res_2426_: u64 = 0;
    let mut v_r_2427_: *mut LeanObject = core::ptr::null_mut();
    v_x_109__boxed_2425_ = lean_unbox_uint64(v_x_2423_);
    lean_dec_ref(v_x_2423_);
    v_res_2426_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v_x_109__boxed_2425_, v_x_2424_);
    lean_dec(v_x_2424_);
    v_r_2427_ = lean_box_uint64(v_res_2426_);
    return v_r_2427_;
}
pub unsafe fn _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0()
-> u64 {
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u64 = 0;
    v___x_2428_ = lean_unsigned_to_nat(1723);
    v___x_2429_ = lean_uint64_of_nat(v___x_2428_);
    return v___x_2429_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(
    mut v_x_2430_: *mut LeanObject,
) -> u64 {
    let mut v_c_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ls_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxArgs_x3f_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: u64 = 0;
    let mut v___y_2436_: u64 = 0;
    let mut v___x_2437_: u64 = 0;
    let mut v___x_2438_: u64 = 0;
    let mut v___x_2439_: u64 = 0;
    let mut v___x_2440_: u64 = 0;
    let mut v___x_2441_: u64 = 0;
    let mut v___x_2442_: u64 = 0;
    let mut v_val_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u64 = 0;
    let mut v___x_2445_: u64 = 0;
    let mut v___x_2446_: u64 = 0;
    let mut v___x_2447_: u64 = 0;
    let mut v___x_2448_: u64 = 0;
    let mut v_hash_2449_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_c_2431_ = lean_ctor_get(v_x_2430_, 0);
                v_ls_2432_ = lean_ctor_get(v_x_2430_, 1);
                v_maxArgs_x3f_2433_ = lean_ctor_get(v_x_2430_, 2);
                v___x_2434_ = 0u64;
                if lean_obj_tag(v_c_2431_) == 0 {
                    v___x_2448_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once), _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
                    v___y_2436_ = v___x_2448_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2449_ = lean_ctor_get_uint64(
                        v_c_2431_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2436_ = v_hash_2449_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2437_ = lean_uint64_mix_hash(v___x_2434_, v___y_2436_);
                v___x_2438_ = 7u64;
                v___x_2439_ = l_List_foldl___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash_spec__0(v___x_2438_, v_ls_2432_);
                v___x_2440_ = lean_uint64_mix_hash(v___x_2437_, v___x_2439_);
                if lean_obj_tag(v_maxArgs_x3f_2433_) == 0 {
                    v___x_2441_ = 11u64;
                    v___x_2442_ = lean_uint64_mix_hash(v___x_2440_, v___x_2441_);
                    return v___x_2442_;
                } else {
                    v_val_2443_ = lean_ctor_get(v_maxArgs_x3f_2433_, 0);
                    v___x_2444_ = lean_uint64_of_nat(v_val_2443_);
                    v___x_2445_ = 13u64;
                    v___x_2446_ = lean_uint64_mix_hash(v___x_2444_, v___x_2445_);
                    v___x_2447_ = lean_uint64_mix_hash(v___x_2440_, v___x_2446_);
                    return v___x_2447_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___boxed(
    mut v_x_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2451_: u64 = 0;
    let mut v_r_2452_: *mut LeanObject = core::ptr::null_mut();
    v_res_2451_ =
        l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_2450_);
    lean_dec_ref(v_x_2450_);
    v_r_2452_ = lean_box_uint64(v_res_2451_);
    return v_r_2452_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(
    mut v_fn_2489_: *mut LeanObject,
    mut v_maxArgs_x3f_2490_: *mut LeanObject,
    mut v_k_2491_: *mut LeanObject,
    mut v_a_2492_: *mut LeanObject,
    mut v_a_2493_: *mut LeanObject,
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funInfo_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finfo_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v_inferType_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funInfo_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_whnf_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqTrans_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqPerm_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2560_: u8 = 0;
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_isSharedCheck_2565_: u8 = 0;
    let mut v_a_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_maxArgs_x3f_2490_);
                lean_inc_ref(v_fn_2489_);
                v___x_2497_ =
                    l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_2489_, v_maxArgs_x3f_2490_, v_a_2492_);
                if lean_obj_tag(v___x_2497_) == 0 {
                    v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
                    v_isSharedCheck_2565_ = (!lean_is_exclusive(v___x_2497_)) as u8;
                    if v_isSharedCheck_2565_ == 0 {
                        v___x_2500_ = v___x_2497_;
                        v_isShared_2501_ = v_isSharedCheck_2565_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2498_);
                        lean_dec(v___x_2497_);
                        v___x_2500_ = lean_box(0);
                        v_isShared_2501_ = v_isSharedCheck_2565_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_k_2491_);
                    lean_dec(v_maxArgs_x3f_2490_);
                    lean_dec_ref(v_fn_2489_);
                    v_a_2566_ = lean_ctor_get(v___x_2497_, 0);
                    v_isSharedCheck_2573_ = (!lean_is_exclusive(v___x_2497_)) as u8;
                    if v_isSharedCheck_2573_ == 0 {
                        v___x_2568_ = v___x_2497_;
                        v_isShared_2569_ = v_isSharedCheck_2573_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2566_);
                        lean_dec(v___x_2497_);
                        v___x_2568_ = lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2573_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2502_ = lean_st_ref_get(v_a_2493_);
                v_cache_2503_ = lean_ctor_get(v___x_2502_, 1);
                lean_inc_ref(v_cache_2503_);
                lean_dec(v___x_2502_);
                v_funInfo_2504_ = lean_ctor_get(v_cache_2503_, 1);
                lean_inc_ref(v_funInfo_2504_);
                lean_dec_ref(v_cache_2503_);
                v___x_2505_ =
                    l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__0;
                v___x_2506_ =
                    l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__1;
                lean_inc(v_a_2498_);
                v___x_2541_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_2505_,
                    v___x_2506_,
                    v_funInfo_2504_,
                    v_a_2498_,
                );
                lean_dec_ref(v_funInfo_2504_);
                if lean_obj_tag(v___x_2541_) == 0 {
                    if lean_obj_tag(v_fn_2489_) == 4 {
                        v_declName_2542_ = lean_ctor_get(v_fn_2489_, 0);
                        lean_inc(v_declName_2542_);
                        v_us_2543_ = lean_ctor_get(v_fn_2489_, 1);
                        lean_inc_n(v_us_2543_, 2);
                        lean_dec_ref_known(v_fn_2489_, 2);
                        v___f_2544_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___closed__2;
                        v___x_2545_ = l_List_any___redArg(v_us_2543_, v___f_2544_);
                        if v___x_2545_ == 0 {
                            v___x_2546_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey___closed__0;
                            v___x_2547_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey___closed__0;
                            v___x_2548_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_;
                            v___x_2549_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
                            lean_inc(v_declName_2542_);
                            v___x_2550_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_2550_, 0, v_declName_2542_);
                            lean_ctor_set(v___x_2550_, 1, v_us_2543_);
                            lean_ctor_set(v___x_2550_, 2, v_maxArgs_x3f_2490_);
                            v___x_2551_ = l_Lean_Meta_realizeValue___redArg(
                                v___x_2546_,
                                v___x_2547_,
                                v___x_2548_,
                                v___x_2549_,
                                v_declName_2542_,
                                v___x_2550_,
                                v_k_2491_,
                                v_a_2492_,
                                v_a_2493_,
                                v_a_2494_,
                                v_a_2495_,
                            );
                            if lean_obj_tag(v___x_2551_) == 0 {
                                v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
                                lean_inc(v_a_2552_);
                                lean_dec_ref_known(v___x_2551_, 1);
                                v_finfo_2508_ = v_a_2552_;
                                v___y_2509_ = v_a_2493_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2500_);
                                lean_dec(v_a_2498_);
                                return v___x_2551_;
                            }
                        } else {
                            lean_dec(v_us_2543_);
                            lean_dec(v_declName_2542_);
                            lean_dec(v_maxArgs_x3f_2490_);
                            lean_inc(v_a_2495_);
                            lean_inc_ref(v_a_2494_);
                            lean_inc(v_a_2493_);
                            lean_inc_ref(v_a_2492_);
                            v___x_2553_ = lean_apply_5(
                                v_k_2491_,
                                v_a_2492_,
                                v_a_2493_,
                                v_a_2494_,
                                v_a_2495_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_2553_) == 0 {
                                v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
                                lean_inc(v_a_2554_);
                                lean_dec_ref_known(v___x_2553_, 1);
                                v_finfo_2508_ = v_a_2554_;
                                v___y_2509_ = v_a_2493_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2500_);
                                lean_dec(v_a_2498_);
                                return v___x_2553_;
                            }
                        }
                    } else {
                        lean_dec(v_maxArgs_x3f_2490_);
                        lean_dec_ref(v_fn_2489_);
                        lean_inc(v_a_2495_);
                        lean_inc_ref(v_a_2494_);
                        lean_inc(v_a_2493_);
                        lean_inc_ref(v_a_2492_);
                        v___x_2555_ = lean_apply_5(
                            v_k_2491_,
                            v_a_2492_,
                            v_a_2493_,
                            v_a_2494_,
                            v_a_2495_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_2555_) == 0 {
                            v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
                            lean_inc(v_a_2556_);
                            lean_dec_ref_known(v___x_2555_, 1);
                            v_finfo_2508_ = v_a_2556_;
                            v___y_2509_ = v_a_2493_;
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_2500_);
                            lean_dec(v_a_2498_);
                            return v___x_2555_;
                        }
                    }
                } else {
                    lean_del_object(v___x_2500_);
                    lean_dec(v_a_2498_);
                    lean_dec_ref(v_k_2491_);
                    lean_dec(v_maxArgs_x3f_2490_);
                    lean_dec_ref(v_fn_2489_);
                    v_val_2557_ = lean_ctor_get(v___x_2541_, 0);
                    v_isSharedCheck_2564_ = (!lean_is_exclusive(v___x_2541_)) as u8;
                    if v_isSharedCheck_2564_ == 0 {
                        v___x_2559_ = v___x_2541_;
                        v_isShared_2560_ = v_isSharedCheck_2564_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_2557_);
                        lean_dec(v___x_2541_);
                        v___x_2559_ = lean_box(0);
                        v_isShared_2560_ = v_isSharedCheck_2564_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2510_ = lean_st_ref_take(v___y_2509_);
                v_cache_2511_ = lean_ctor_get(v___x_2510_, 1);
                v_mctx_2512_ = lean_ctor_get(v___x_2510_, 0);
                v_zetaDeltaFVarIds_2513_ = lean_ctor_get(v___x_2510_, 2);
                v_postponed_2514_ = lean_ctor_get(v___x_2510_, 3);
                v_diag_2515_ = lean_ctor_get(v___x_2510_, 4);
                v_isSharedCheck_2540_ = (!lean_is_exclusive(v___x_2510_)) as u8;
                if v_isSharedCheck_2540_ == 0 {
                    v___x_2517_ = v___x_2510_;
                    v_isShared_2518_ = v_isSharedCheck_2540_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_2515_);
                    lean_inc(v_postponed_2514_);
                    lean_inc(v_zetaDeltaFVarIds_2513_);
                    lean_inc(v_cache_2511_);
                    lean_inc(v_mctx_2512_);
                    lean_dec(v___x_2510_);
                    v___x_2517_ = lean_box(0);
                    v_isShared_2518_ = v_isSharedCheck_2540_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_inferType_2519_ = lean_ctor_get(v_cache_2511_, 0);
                v_funInfo_2520_ = lean_ctor_get(v_cache_2511_, 1);
                v_synthInstance_2521_ = lean_ctor_get(v_cache_2511_, 2);
                v_whnf_2522_ = lean_ctor_get(v_cache_2511_, 3);
                v_defEqTrans_2523_ = lean_ctor_get(v_cache_2511_, 4);
                v_defEqPerm_2524_ = lean_ctor_get(v_cache_2511_, 5);
                v_isSharedCheck_2539_ = (!lean_is_exclusive(v_cache_2511_)) as u8;
                if v_isSharedCheck_2539_ == 0 {
                    v___x_2526_ = v_cache_2511_;
                    v_isShared_2527_ = v_isSharedCheck_2539_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_defEqPerm_2524_);
                    lean_inc(v_defEqTrans_2523_);
                    lean_inc(v_whnf_2522_);
                    lean_inc(v_synthInstance_2521_);
                    lean_inc(v_funInfo_2520_);
                    lean_inc(v_inferType_2519_);
                    lean_dec(v_cache_2511_);
                    v___x_2526_ = lean_box(0);
                    v_isShared_2527_ = v_isSharedCheck_2539_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v_finfo_2508_);
                v___x_2528_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___x_2505_,
                    v___x_2506_,
                    v_funInfo_2520_,
                    v_a_2498_,
                    v_finfo_2508_,
                );
                if v_isShared_2527_ == 0 {
                    lean_ctor_set(v___x_2526_, 1, v___x_2528_);
                    v___x_2530_ = v___x_2526_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_inferType_2519_);
                    lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2528_);
                    lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_synthInstance_2521_);
                    lean_ctor_set(v_reuseFailAlloc_2538_, 3, v_whnf_2522_);
                    lean_ctor_set(v_reuseFailAlloc_2538_, 4, v_defEqTrans_2523_);
                    lean_ctor_set(v_reuseFailAlloc_2538_, 5, v_defEqPerm_2524_);
                    v___x_2530_ = v_reuseFailAlloc_2538_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2518_ == 0 {
                    lean_ctor_set(v___x_2517_, 1, v___x_2530_);
                    v___x_2532_ = v___x_2517_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_mctx_2512_);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2530_);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_zetaDeltaFVarIds_2513_);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_postponed_2514_);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_diag_2515_);
                    v___x_2532_ = v_reuseFailAlloc_2537_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2533_ = lean_st_ref_set(v___y_2509_, v___x_2532_);
                if v_isShared_2501_ == 0 {
                    lean_ctor_set(v___x_2500_, 0, v_finfo_2508_);
                    v___x_2535_ = v___x_2500_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_finfo_2508_);
                    v___x_2535_ = v_reuseFailAlloc_2536_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2535_;
            }
            8 => {
                if v_isShared_2560_ == 0 {
                    lean_ctor_set_tag(v___x_2559_, 0);
                    v___x_2562_ = v___x_2559_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_val_2557_);
                    v___x_2562_ = v_reuseFailAlloc_2563_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2562_;
            }
            10 => {
                if v_isShared_2569_ == 0 {
                    v___x_2571_ = v___x_2568_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
                    v___x_2571_ = v_reuseFailAlloc_2572_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___boxed(
    mut v_fn_2574_: *mut LeanObject,
    mut v_maxArgs_x3f_2575_: *mut LeanObject,
    mut v_k_2576_: *mut LeanObject,
    mut v_a_2577_: *mut LeanObject,
    mut v_a_2578_: *mut LeanObject,
    mut v_a_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2582_: *mut LeanObject = core::ptr::null_mut();
    v_res_2582_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(
        v_fn_2574_,
        v_maxArgs_x3f_2575_,
        v_k_2576_,
        v_a_2577_,
        v_a_2578_,
        v_a_2579_,
        v_a_2580_,
    );
    lean_dec(v_a_2580_);
    lean_dec_ref(v_a_2579_);
    lean_dec(v_a_2578_);
    lean_dec_ref(v_a_2577_);
    return v_res_2582_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(
    mut v_e_2583_: *mut LeanObject,
    mut v_deps_2584_: *mut LeanObject,
    mut v_k_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2586_: u8 = 0;
    v___x_2586_ = l_Lean_Expr_hasFVar(v_e_2583_);
    if v___x_2586_ == 0 {
        lean_dec(v_k_2585_);
        return v_deps_2584_;
    } else {
        let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
        v___x_2587_ = lean_apply_1(v_k_2585_, v_deps_2584_);
        return v___x_2587_;
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(
    mut v_e_2588_: *mut LeanObject,
    mut v_deps_2589_: *mut LeanObject,
    mut v_k_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2591_: *mut LeanObject = core::ptr::null_mut();
    v_res_2591_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(
        v_e_2588_,
        v_deps_2589_,
        v_k_2590_,
    );
    lean_dec_ref(v_e_2588_);
    return v_res_2591_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(
    mut v_00_u03b1_2592_: *mut LeanObject,
    mut v_e_2593_: *mut LeanObject,
    mut v_deps_2594_: *mut LeanObject,
    mut v_k_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: u8 = 0;
    v___x_2596_ = l_Lean_Expr_hasFVar(v_e_2593_);
    if v___x_2596_ == 0 {
        lean_dec(v_k_2595_);
        return v_deps_2594_;
    } else {
        let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
        v___x_2597_ = lean_apply_1(v_k_2595_, v_deps_2594_);
        return v___x_2597_;
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(
    mut v_00_u03b1_2598_: *mut LeanObject,
    mut v_e_2599_: *mut LeanObject,
    mut v_deps_2600_: *mut LeanObject,
    mut v_k_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2602_: *mut LeanObject = core::ptr::null_mut();
    v_res_2602_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(
        v_00_u03b1_2598_,
        v_e_2599_,
        v_deps_2600_,
        v_k_2601_,
    );
    lean_dec_ref(v_e_2599_);
    return v_res_2602_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(
    mut v_xs_2603_: *mut LeanObject,
    mut v_v_2604_: *mut LeanObject,
    mut v_i_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: u8 = 0;
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2606_ = lean_array_get_size(v_xs_2603_);
                v___x_2607_ = lean_nat_dec_lt(v_i_2605_, v___x_2606_);
                if v___x_2607_ == 0 {
                    lean_dec(v_i_2605_);
                    v___x_2608_ = lean_box(0);
                    return v___x_2608_;
                } else {
                    v___x_2609_ = lean_array_fget_borrowed(v_xs_2603_, v_i_2605_);
                    v___x_2610_ = lean_expr_eqv(v___x_2609_, v_v_2604_);
                    if v___x_2610_ == 0 {
                        v___x_2611_ = lean_unsigned_to_nat(1);
                        v___x_2612_ = lean_nat_add(v_i_2605_, v___x_2611_);
                        lean_dec(v_i_2605_);
                        v_i_2605_ = v___x_2612_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2614_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2614_, 0, v_i_2605_);
                        return v___x_2614_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1___boxed(
    mut v_xs_2615_: *mut LeanObject,
    mut v_v_2616_: *mut LeanObject,
    mut v_i_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2618_: *mut LeanObject = core::ptr::null_mut();
    v_res_2618_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_2615_, v_v_2616_, v_i_2617_);
    lean_dec_ref(v_v_2616_);
    lean_dec_ref(v_xs_2615_);
    return v_res_2618_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(
    mut v_xs_2619_: *mut LeanObject,
    mut v_v_2620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    v___x_2621_ = lean_unsigned_to_nat(0);
    v___x_2622_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__1(v_xs_2619_, v_v_2620_, v___x_2621_);
    return v___x_2622_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(
    mut v_xs_2623_: *mut LeanObject,
    mut v_v_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_2623_, v_v_2624_);
    lean_dec_ref(v_v_2624_);
    lean_dec_ref(v_xs_2623_);
    return v_res_2625_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(
    mut v_xs_2626_: *mut LeanObject,
    mut v_v_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2633_: u8 = 0;
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2628_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(v_xs_2626_, v_v_2627_);
                if lean_obj_tag(v___x_2628_) == 0 {
                    v___x_2629_ = lean_box(0);
                    return v___x_2629_;
                } else {
                    v_val_2630_ = lean_ctor_get(v___x_2628_, 0);
                    v_isSharedCheck_2637_ = (!lean_is_exclusive(v___x_2628_)) as u8;
                    if v_isSharedCheck_2637_ == 0 {
                        v___x_2632_ = v___x_2628_;
                        v_isShared_2633_ = v_isSharedCheck_2637_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2630_);
                        lean_dec(v___x_2628_);
                        v___x_2632_ = lean_box(0);
                        v_isShared_2633_ = v_isSharedCheck_2637_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2633_ == 0 {
                    v___x_2635_ = v___x_2632_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_val_2630_);
                    v___x_2635_ = v_reuseFailAlloc_2636_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(
    mut v_xs_2638_: *mut LeanObject,
    mut v_v_2639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2640_: *mut LeanObject = core::ptr::null_mut();
    v_res_2640_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_xs_2638_, v_v_2639_);
    lean_dec_ref(v_v_2639_);
    lean_dec_ref(v_xs_2638_);
    return v_res_2640_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(
    mut v_a_2641_: *mut LeanObject,
    mut v_as_2642_: *mut LeanObject,
    mut v_i_2643_: usize,
    mut v_stop_2644_: usize,
) -> u8 {
    let mut v___x_2645_: u8 = 0;
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    let mut v___x_2648_: usize = 0;
    let mut v___x_2649_: usize = 0;
    let mut v___x_2651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2645_ = lean_usize_dec_eq(v_i_2643_, v_stop_2644_);
                if v___x_2645_ == 0 {
                    v___x_2646_ = lean_array_uget_borrowed(v_as_2642_, v_i_2643_);
                    v___x_2647_ = lean_nat_dec_eq(v_a_2641_, v___x_2646_);
                    if v___x_2647_ == 0 {
                        v___x_2648_ = 1usize;
                        v___x_2649_ = lean_usize_add(v_i_2643_, v___x_2648_);
                        v_i_2643_ = v___x_2649_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2647_;
                    }
                } else {
                    v___x_2651_ = 0;
                    return v___x_2651_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2___boxed(
    mut v_a_2652_: *mut LeanObject,
    mut v_as_2653_: *mut LeanObject,
    mut v_i_2654_: *mut LeanObject,
    mut v_stop_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2656_: usize = 0;
    let mut v_stop_boxed_2657_: usize = 0;
    let mut v_res_2658_: u8 = 0;
    let mut v_r_2659_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2656_ = lean_unbox_usize(v_i_2654_);
    lean_dec(v_i_2654_);
    v_stop_boxed_2657_ = lean_unbox_usize(v_stop_2655_);
    lean_dec(v_stop_2655_);
    v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_2652_, v_as_2653_, v_i_boxed_2656_, v_stop_boxed_2657_);
    lean_dec_ref(v_as_2653_);
    lean_dec(v_a_2652_);
    v_r_2659_ = lean_box((v_res_2658_) as usize);
    return v_r_2659_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(
    mut v_as_2660_: *mut LeanObject,
    mut v_a_2661_: *mut LeanObject,
) -> u8 {
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    v___x_2662_ = lean_unsigned_to_nat(0);
    v___x_2663_ = lean_array_get_size(v_as_2660_);
    v___x_2664_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
    if v___x_2664_ == 0 {
        return v___x_2664_;
    } else {
        if v___x_2664_ == 0 {
            return v___x_2664_;
        } else {
            let mut v___x_2665_: usize = 0;
            let mut v___x_2666_: usize = 0;
            let mut v___x_2667_: u8 = 0;
            v___x_2665_ = 0usize;
            v___x_2666_ = lean_usize_of_nat(v___x_2663_);
            v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1_spec__2(v_a_2661_, v_as_2660_, v___x_2665_, v___x_2666_);
            return v___x_2667_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1___boxed(
    mut v_as_2668_: *mut LeanObject,
    mut v_a_2669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2670_: u8 = 0;
    let mut v_r_2671_: *mut LeanObject = core::ptr::null_mut();
    v_res_2670_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_as_2668_, v_a_2669_);
    lean_dec(v_a_2669_);
    lean_dec_ref(v_as_2668_);
    v_r_2671_ = lean_box((v_res_2670_) as usize);
    return v_r_2671_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(
    mut v_fvars_2672_: *mut LeanObject,
    mut v_e_2673_: *mut LeanObject,
    mut v_deps_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: u8 = 0;
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2673_) {
                5 => {
                    v_fn_2681_ = lean_ctor_get(v_e_2673_, 0);
                    v_arg_2682_ = lean_ctor_get(v_e_2673_, 1);
                    v___x_2683_ = l_Lean_Expr_hasFVar(v_e_2673_);
                    if v___x_2683_ == 0 {
                        return v_deps_2674_;
                    } else {
                        v___x_2684_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(
                            v_fvars_2672_,
                            v_fn_2681_,
                            v_deps_2674_,
                        );
                        v_e_2673_ = v_arg_2682_;
                        v_deps_2674_ = v___x_2684_;
                        state = 0;
                        continue;
                    }
                }
                7 => {
                    v_binderType_2686_ = lean_ctor_get(v_e_2673_, 1);
                    v_body_2687_ = lean_ctor_get(v_e_2673_, 2);
                    v_d_2676_ = v_binderType_2686_;
                    v_b_2677_ = v_body_2687_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_2688_ = lean_ctor_get(v_e_2673_, 1);
                    v_body_2689_ = lean_ctor_get(v_e_2673_, 2);
                    v_d_2676_ = v_binderType_2688_;
                    v_b_2677_ = v_body_2689_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_2690_ = lean_ctor_get(v_e_2673_, 1);
                    v_value_2691_ = lean_ctor_get(v_e_2673_, 2);
                    v_body_2692_ = lean_ctor_get(v_e_2673_, 3);
                    v___x_2693_ = l_Lean_Expr_hasFVar(v_e_2673_);
                    if v___x_2693_ == 0 {
                        return v_deps_2674_;
                    } else {
                        v___x_2694_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(
                            v_fvars_2672_,
                            v_type_2690_,
                            v_deps_2674_,
                        );
                        v___x_2695_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(
                            v_fvars_2672_,
                            v_value_2691_,
                            v___x_2694_,
                        );
                        v_e_2673_ = v_body_2692_;
                        v_deps_2674_ = v___x_2695_;
                        state = 0;
                        continue;
                    }
                }
                11 => {
                    v_struct_2697_ = lean_ctor_get(v_e_2673_, 2);
                    v_e_2673_ = v_struct_2697_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_2699_ = lean_ctor_get(v_e_2673_, 1);
                    v_e_2673_ = v_expr_2699_;
                    state = 0;
                    continue;
                }
                1 => {
                    v___x_2701_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_2672_, v_e_2673_);
                    if lean_obj_tag(v___x_2701_) == 0 {
                        return v_deps_2674_;
                    } else {
                        v_val_2702_ = lean_ctor_get(v___x_2701_, 0);
                        lean_inc(v_val_2702_);
                        lean_dec_ref_known(v___x_2701_, 1);
                        v___x_2703_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_deps_2674_, v_val_2702_);
                        if v___x_2703_ == 0 {
                            v___x_2704_ = lean_array_push(v_deps_2674_, v_val_2702_);
                            return v___x_2704_;
                        } else {
                            lean_dec(v_val_2702_);
                            return v_deps_2674_;
                        }
                    }
                }
                _ => {
                    return v_deps_2674_;
                }
            },
            1 => {
                v___x_2678_ = l_Lean_Expr_hasFVar(v_e_2673_);
                if v___x_2678_ == 0 {
                    return v_deps_2674_;
                } else {
                    v___x_2679_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(
                        v_fvars_2672_,
                        v_d_2676_,
                        v_deps_2674_,
                    );
                    v_e_2673_ = v_b_2677_;
                    v_deps_2674_ = v___x_2679_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(
    mut v_fvars_2705_: *mut LeanObject,
    mut v_e_2706_: *mut LeanObject,
    mut v_deps_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2708_: *mut LeanObject = core::ptr::null_mut();
    v_res_2708_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(
        v_fvars_2705_,
        v_e_2706_,
        v_deps_2707_,
    );
    lean_dec_ref(v_e_2706_);
    lean_dec_ref(v_fvars_2705_);
    return v_res_2708_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(
    mut v_hi_2709_: *mut LeanObject,
    mut v_pivot_2710_: *mut LeanObject,
    mut v_as_2711_: *mut LeanObject,
    mut v_i_2712_: *mut LeanObject,
    mut v_k_2713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: u8 = 0;
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2714_ = lean_nat_dec_lt(v_k_2713_, v_hi_2709_);
                if v___x_2714_ == 0 {
                    lean_dec(v_k_2713_);
                    v___x_2715_ = lean_array_fswap(v_as_2711_, v_i_2712_, v_hi_2709_);
                    v___x_2716_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2716_, 0, v_i_2712_);
                    lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                    return v___x_2716_;
                } else {
                    v___x_2717_ = lean_array_fget_borrowed(v_as_2711_, v_k_2713_);
                    v___x_2718_ = lean_nat_dec_lt(v___x_2717_, v_pivot_2710_);
                    if v___x_2718_ == 0 {
                        v___x_2719_ = lean_unsigned_to_nat(1);
                        v___x_2720_ = lean_nat_add(v_k_2713_, v___x_2719_);
                        lean_dec(v_k_2713_);
                        v_k_2713_ = v___x_2720_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2722_ = lean_array_fswap(v_as_2711_, v_i_2712_, v_k_2713_);
                        v___x_2723_ = lean_unsigned_to_nat(1);
                        v___x_2724_ = lean_nat_add(v_i_2712_, v___x_2723_);
                        lean_dec(v_i_2712_);
                        v___x_2725_ = lean_nat_add(v_k_2713_, v___x_2723_);
                        lean_dec(v_k_2713_);
                        v_as_2711_ = v___x_2722_;
                        v_i_2712_ = v___x_2724_;
                        v_k_2713_ = v___x_2725_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg___boxed(
    mut v_hi_2727_: *mut LeanObject,
    mut v_pivot_2728_: *mut LeanObject,
    mut v_as_2729_: *mut LeanObject,
    mut v_i_2730_: *mut LeanObject,
    mut v_k_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2732_: *mut LeanObject = core::ptr::null_mut();
    v_res_2732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_2727_, v_pivot_2728_, v_as_2729_, v_i_2730_, v_k_2731_);
    lean_dec(v_pivot_2728_);
    lean_dec(v_hi_2727_);
    return v_res_2732_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(
    mut v_n_2733_: *mut LeanObject,
    mut v_as_2734_: *mut LeanObject,
    mut v_lo_2735_: *mut LeanObject,
    mut v_hi_2736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: u8 = 0;
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2748_ = lean_nat_dec_lt(v_lo_2735_, v_hi_2736_);
                if v___x_2748_ == 0 {
                    lean_dec(v_lo_2735_);
                    return v_as_2734_;
                } else {
                    v___x_2749_ = lean_nat_add(v_lo_2735_, v_hi_2736_);
                    v___x_2750_ = lean_unsigned_to_nat(1);
                    v_mid_2751_ = lean_nat_shiftr(v___x_2749_, v___x_2750_);
                    lean_dec(v___x_2749_);
                    v___x_2764_ = lean_array_fget_borrowed(v_as_2734_, v_mid_2751_);
                    v___x_2765_ = lean_array_fget_borrowed(v_as_2734_, v_lo_2735_);
                    v___x_2766_ = lean_nat_dec_lt(v___x_2764_, v___x_2765_);
                    if v___x_2766_ == 0 {
                        v___y_2759_ = v_as_2734_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2767_ = lean_array_fswap(v_as_2734_, v_lo_2735_, v_mid_2751_);
                        v___y_2759_ = v___x_2767_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2739_ = lean_array_fget(v___y_2738_, v_hi_2736_);
                lean_inc_n(v_lo_2735_, 2);
                v___x_2740_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_2736_, v_pivot_2739_, v___y_2738_, v_lo_2735_, v_lo_2735_);
                lean_dec(v_pivot_2739_);
                v_fst_2741_ = lean_ctor_get(v___x_2740_, 0);
                lean_inc(v_fst_2741_);
                v_snd_2742_ = lean_ctor_get(v___x_2740_, 1);
                lean_inc(v_snd_2742_);
                lean_dec_ref(v___x_2740_);
                v___x_2743_ = lean_nat_dec_le(v_hi_2736_, v_fst_2741_);
                if v___x_2743_ == 0 {
                    v___x_2744_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_2733_, v_snd_2742_, v_lo_2735_, v_fst_2741_);
                    v___x_2745_ = lean_unsigned_to_nat(1);
                    v___x_2746_ = lean_nat_add(v_fst_2741_, v___x_2745_);
                    lean_dec(v_fst_2741_);
                    v_as_2734_ = v___x_2744_;
                    v_lo_2735_ = v___x_2746_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_2741_);
                    lean_dec(v_lo_2735_);
                    return v_snd_2742_;
                }
            }
            2 => {
                v___x_2754_ = lean_array_fget_borrowed(v___y_2753_, v_mid_2751_);
                v___x_2755_ = lean_array_fget_borrowed(v___y_2753_, v_hi_2736_);
                v___x_2756_ = lean_nat_dec_lt(v___x_2754_, v___x_2755_);
                if v___x_2756_ == 0 {
                    lean_dec(v_mid_2751_);
                    v___y_2738_ = v___y_2753_;
                    state = 1;
                    continue;
                } else {
                    v___x_2757_ = lean_array_fswap(v___y_2753_, v_mid_2751_, v_hi_2736_);
                    lean_dec(v_mid_2751_);
                    v___y_2738_ = v___x_2757_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2760_ = lean_array_fget_borrowed(v___y_2759_, v_hi_2736_);
                v___x_2761_ = lean_array_fget_borrowed(v___y_2759_, v_lo_2735_);
                v___x_2762_ = lean_nat_dec_lt(v___x_2760_, v___x_2761_);
                if v___x_2762_ == 0 {
                    v___y_2753_ = v___y_2759_;
                    state = 2;
                    continue;
                } else {
                    v___x_2763_ = lean_array_fswap(v___y_2759_, v_lo_2735_, v_hi_2736_);
                    v___y_2753_ = v___x_2763_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(
    mut v_n_2768_: *mut LeanObject,
    mut v_as_2769_: *mut LeanObject,
    mut v_lo_2770_: *mut LeanObject,
    mut v_hi_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2772_: *mut LeanObject = core::ptr::null_mut();
    v_res_2772_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_2768_, v_as_2769_, v_lo_2770_, v_hi_2771_);
    lean_dec(v_hi_2771_);
    lean_dec(v_n_2768_);
    return v_res_2772_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(
    mut v_fvars_2775_: *mut LeanObject,
    mut v_e_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deps_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: u8 = 0;
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2777_ = lean_unsigned_to_nat(0);
                v___x_2778_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__0;
                v_deps_2779_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(
                    v_fvars_2775_,
                    v_e_2776_,
                    v___x_2778_,
                );
                v___x_2780_ = lean_array_get_size(v_deps_2779_);
                v___x_2781_ = lean_nat_dec_eq(v___x_2780_, v___x_2777_);
                if v___x_2781_ == 0 {
                    v___x_2782_ = lean_unsigned_to_nat(1);
                    v___x_2783_ = lean_nat_sub(v___x_2780_, v___x_2782_);
                    v___x_2789_ = lean_nat_dec_le(v___x_2777_, v___x_2783_);
                    if v___x_2789_ == 0 {
                        lean_inc(v___x_2783_);
                        v___y_2785_ = v___x_2783_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2785_ = v___x_2777_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_deps_2779_;
                }
            }
            1 => {
                v___x_2786_ = lean_nat_dec_le(v___y_2785_, v___x_2783_);
                if v___x_2786_ == 0 {
                    lean_dec(v___x_2783_);
                    lean_inc(v___y_2785_);
                    v___x_2787_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_2780_, v_deps_2779_, v___y_2785_, v___y_2785_);
                    lean_dec(v___y_2785_);
                    return v___x_2787_;
                } else {
                    v___x_2788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v___x_2780_, v_deps_2779_, v___y_2785_, v___x_2783_);
                    lean_dec(v___x_2783_);
                    return v___x_2788_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(
    mut v_fvars_2790_: *mut LeanObject,
    mut v_e_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2792_: *mut LeanObject = core::ptr::null_mut();
    v_res_2792_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(v_fvars_2790_, v_e_2791_);
    lean_dec_ref(v_e_2791_);
    lean_dec_ref(v_fvars_2790_);
    return v_res_2792_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(
    mut v_n_2793_: *mut LeanObject,
    mut v_as_2794_: *mut LeanObject,
    mut v_lo_2795_: *mut LeanObject,
    mut v_hi_2796_: *mut LeanObject,
    mut v_w_2797_: *mut LeanObject,
    mut v_hlo_2798_: *mut LeanObject,
    mut v_hhi_2799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    v___x_2800_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(v_n_2793_, v_as_2794_, v_lo_2795_, v_hi_2796_);
    return v___x_2800_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(
    mut v_n_2801_: *mut LeanObject,
    mut v_as_2802_: *mut LeanObject,
    mut v_lo_2803_: *mut LeanObject,
    mut v_hi_2804_: *mut LeanObject,
    mut v_w_2805_: *mut LeanObject,
    mut v_hlo_2806_: *mut LeanObject,
    mut v_hhi_2807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2808_: *mut LeanObject = core::ptr::null_mut();
    v_res_2808_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(v_n_2801_, v_as_2802_, v_lo_2803_, v_hi_2804_, v_w_2805_, v_hlo_2806_, v_hhi_2807_);
    lean_dec(v_hi_2804_);
    lean_dec(v_n_2801_);
    return v_res_2808_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(
    mut v_n_2809_: *mut LeanObject,
    mut v_lo_2810_: *mut LeanObject,
    mut v_hi_2811_: *mut LeanObject,
    mut v_hhi_2812_: *mut LeanObject,
    mut v_pivot_2813_: *mut LeanObject,
    mut v_as_2814_: *mut LeanObject,
    mut v_i_2815_: *mut LeanObject,
    mut v_k_2816_: *mut LeanObject,
    mut v_ilo_2817_: *mut LeanObject,
    mut v_ik_2818_: *mut LeanObject,
    mut v_w_2819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    v___x_2820_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___redArg(v_hi_2811_, v_pivot_2813_, v_as_2814_, v_i_2815_, v_k_2816_);
    return v___x_2820_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0___boxed(
    mut v_n_2821_: *mut LeanObject,
    mut v_lo_2822_: *mut LeanObject,
    mut v_hi_2823_: *mut LeanObject,
    mut v_hhi_2824_: *mut LeanObject,
    mut v_pivot_2825_: *mut LeanObject,
    mut v_as_2826_: *mut LeanObject,
    mut v_i_2827_: *mut LeanObject,
    mut v_k_2828_: *mut LeanObject,
    mut v_ilo_2829_: *mut LeanObject,
    mut v_ik_2830_: *mut LeanObject,
    mut v_w_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2832_: *mut LeanObject = core::ptr::null_mut();
    v_res_2832_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0_spec__0(v_n_2821_, v_lo_2822_, v_hi_2823_, v_hhi_2824_, v_pivot_2825_, v_as_2826_, v_i_2827_, v_k_2828_, v_ilo_2829_, v_ik_2830_, v_w_2831_);
    lean_dec(v_pivot_2825_);
    lean_dec(v_hi_2823_);
    lean_dec(v_lo_2822_);
    lean_dec(v_n_2821_);
    return v_res_2832_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(
    mut v_backDeps_2833_: *mut LeanObject,
    mut v_as_2834_: *mut LeanObject,
    mut v_i_2835_: *mut LeanObject,
    mut v_j_2836_: *mut LeanObject,
    mut v_bs_2837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2839_: u8 = 0;
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2841_: u8 = 0;
    let mut v_hasFwdDeps_2842_: u8 = 0;
    let mut v_backDeps_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isProp_2844_: u8 = 0;
    let mut v_isDecInst_2845_: u8 = 0;
    let mut v_isInstance_2846_: u8 = 0;
    let mut v_higherOrderOutParam_2847_: u8 = 0;
    let mut v_dependsOnHigherOrderOutParam_2848_: u8 = 0;
    let mut v_one_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2859_: u8 = 0;
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut v_unused_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2838_ = lean_unsigned_to_nat(0);
                v_isZero_2839_ = lean_nat_dec_eq(v_i_2835_, v_zero_2838_);
                if v_isZero_2839_ == 1 {
                    lean_dec(v_j_2836_);
                    lean_dec(v_i_2835_);
                    return v_bs_2837_;
                } else {
                    v___x_2840_ = lean_array_fget(v_as_2834_, v_j_2836_);
                    v_binderInfo_2841_ = lean_ctor_get_uint8(
                        v___x_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_hasFwdDeps_2842_ = lean_ctor_get_uint8(
                        v___x_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v_backDeps_2843_ = lean_ctor_get(v___x_2840_, 0);
                    v_isProp_2844_ = lean_ctor_get_uint8(
                        v___x_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    );
                    v_isDecInst_2845_ = lean_ctor_get_uint8(
                        v___x_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                    );
                    v_isInstance_2846_ = lean_ctor_get_uint8(
                        v___x_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                    );
                    v_higherOrderOutParam_2847_ = lean_ctor_get_uint8(
                        v___x_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 5) as u32,
                    );
                    v_dependsOnHigherOrderOutParam_2848_ = lean_ctor_get_uint8(
                        v___x_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 6) as u32,
                    );
                    v_one_2849_ = lean_unsigned_to_nat(1);
                    v_n_2850_ = lean_nat_sub(v_i_2835_, v_one_2849_);
                    lean_dec(v_i_2835_);
                    if v_hasFwdDeps_2842_ == 0 {
                        v___x_2856_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_backDeps_2833_, v_j_2836_);
                        if v___x_2856_ == 0 {
                            v___y_2852_ = v___x_2840_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc_ref(v_backDeps_2843_);
                            v_isSharedCheck_2863_ = (!lean_is_exclusive(v___x_2840_)) as u8;
                            if v_isSharedCheck_2863_ == 0 {
                                v_unused_2864_ = lean_ctor_get(v___x_2840_, 0);
                                lean_dec(v_unused_2864_);
                                v___x_2858_ = v___x_2840_;
                                v_isShared_2859_ = v_isSharedCheck_2863_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_2840_);
                                v___x_2858_ = lean_box(0);
                                v_isShared_2859_ = v_isSharedCheck_2863_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___y_2852_ = v___x_2840_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2853_ = lean_nat_add(v_j_2836_, v_one_2849_);
                lean_dec(v_j_2836_);
                v___x_2854_ = lean_array_push(v_bs_2837_, v___y_2852_);
                v_i_2835_ = v_n_2850_;
                v_j_2836_ = v___x_2853_;
                v_bs_2837_ = v___x_2854_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2859_ == 0 {
                    v___x_2861_ = v___x_2858_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, (7) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_backDeps_2843_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_binderInfo_2841_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_isProp_2844_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_isDecInst_2845_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                        v_isInstance_2846_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 5) as u32,
                        v_higherOrderOutParam_2847_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 6) as u32,
                        v_dependsOnHigherOrderOutParam_2848_,
                    );
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_2861_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_2856_,
                );
                v___y_2852_ = v___x_2861_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(
    mut v_backDeps_2865_: *mut LeanObject,
    mut v_as_2866_: *mut LeanObject,
    mut v_i_2867_: *mut LeanObject,
    mut v_j_2868_: *mut LeanObject,
    mut v_bs_2869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2870_: *mut LeanObject = core::ptr::null_mut();
    v_res_2870_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_2865_, v_as_2866_, v_i_2867_, v_j_2868_, v_bs_2869_);
    lean_dec_ref(v_as_2866_);
    lean_dec_ref(v_backDeps_2865_);
    return v_res_2870_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(
    mut v_pinfo_2871_: *mut LeanObject,
    mut v_backDeps_2872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: u8 = 0;
    v___x_2873_ = lean_array_get_size(v_backDeps_2872_);
    v___x_2874_ = lean_unsigned_to_nat(0);
    v___x_2875_ = lean_nat_dec_eq(v___x_2873_, v___x_2874_);
    if v___x_2875_ == 0 {
        let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
        v___x_2876_ = lean_array_get_size(v_pinfo_2871_);
        v___x_2877_ = lean_mk_empty_array_with_capacity(v___x_2876_);
        v___x_2878_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_2872_, v_pinfo_2871_, v___x_2876_, v___x_2874_, v___x_2877_);
        return v___x_2878_;
    } else {
        lean_inc_ref(v_pinfo_2871_);
        return v_pinfo_2871_;
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(
    mut v_pinfo_2879_: *mut LeanObject,
    mut v_backDeps_2880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2881_: *mut LeanObject = core::ptr::null_mut();
    v_res_2881_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(
        v_pinfo_2879_,
        v_backDeps_2880_,
    );
    lean_dec_ref(v_backDeps_2880_);
    lean_dec_ref(v_pinfo_2879_);
    return v_res_2881_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(
    mut v_backDeps_2882_: *mut LeanObject,
    mut v_as_2883_: *mut LeanObject,
    mut v_i_2884_: *mut LeanObject,
    mut v_j_2885_: *mut LeanObject,
    mut v_inv_2886_: *mut LeanObject,
    mut v_bs_2887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    v___x_2888_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(v_backDeps_2882_, v_as_2883_, v_i_2884_, v_j_2885_, v_bs_2887_);
    return v___x_2888_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(
    mut v_backDeps_2889_: *mut LeanObject,
    mut v_as_2890_: *mut LeanObject,
    mut v_i_2891_: *mut LeanObject,
    mut v_j_2892_: *mut LeanObject,
    mut v_inv_2893_: *mut LeanObject,
    mut v_bs_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2895_: *mut LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(v_backDeps_2889_, v_as_2890_, v_i_2891_, v_j_2892_, v_inv_2893_, v_bs_2894_);
    lean_dec_ref(v_as_2890_);
    lean_dec_ref(v_backDeps_2889_);
    return v_res_2895_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(
    mut v_k_2896_: *mut LeanObject,
    mut v_b_2897_: *mut LeanObject,
    mut v_c_2898_: *mut LeanObject,
    mut v___y_2899_: *mut LeanObject,
    mut v___y_2900_: *mut LeanObject,
    mut v___y_2901_: *mut LeanObject,
    mut v___y_2902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2902_);
    lean_inc_ref(v___y_2901_);
    lean_inc(v___y_2900_);
    lean_inc_ref(v___y_2899_);
    v___x_2904_ = lean_apply_7(
        v_k_2896_,
        v_b_2897_,
        v_c_2898_,
        v___y_2899_,
        v___y_2900_,
        v___y_2901_,
        v___y_2902_,
        lean_box(0),
    );
    return v___x_2904_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed(
    mut v_k_2905_: *mut LeanObject,
    mut v_b_2906_: *mut LeanObject,
    mut v_c_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2913_: *mut LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0(v_k_2905_, v_b_2906_, v_c_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
    lean_dec(v___y_2911_);
    lean_dec_ref(v___y_2910_);
    lean_dec(v___y_2909_);
    lean_dec_ref(v___y_2908_);
    return v_res_2913_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(
    mut v_type_2914_: *mut LeanObject,
    mut v_k_2915_: *mut LeanObject,
    mut v_cleanupAnnotations_2916_: u8,
    mut v_whnfType_2917_: u8,
    mut v___y_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_a_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2923_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2923_, 0, v_k_2915_);
                v___x_2924_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_2914_,
                    v___f_2923_,
                    v_cleanupAnnotations_2916_,
                    v_whnfType_2917_,
                    v___y_2918_,
                    v___y_2919_,
                    v___y_2920_,
                    v___y_2921_,
                );
                if lean_obj_tag(v___x_2924_) == 0 {
                    v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
                    v_isSharedCheck_2932_ = (!lean_is_exclusive(v___x_2924_)) as u8;
                    if v_isSharedCheck_2932_ == 0 {
                        v___x_2927_ = v___x_2924_;
                        v_isShared_2928_ = v_isSharedCheck_2932_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2925_);
                        lean_dec(v___x_2924_);
                        v___x_2927_ = lean_box(0);
                        v_isShared_2928_ = v_isSharedCheck_2932_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2933_ = lean_ctor_get(v___x_2924_, 0);
                    v_isSharedCheck_2940_ = (!lean_is_exclusive(v___x_2924_)) as u8;
                    if v_isSharedCheck_2940_ == 0 {
                        v___x_2935_ = v___x_2924_;
                        v_isShared_2936_ = v_isSharedCheck_2940_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2933_);
                        lean_dec(v___x_2924_);
                        v___x_2935_ = lean_box(0);
                        v_isShared_2936_ = v_isSharedCheck_2940_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2928_ == 0 {
                    v___x_2930_ = v___x_2927_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
                    v___x_2930_ = v_reuseFailAlloc_2931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2930_;
            }
            3 => {
                if v_isShared_2936_ == 0 {
                    v___x_2938_ = v___x_2935_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
                    v___x_2938_ = v_reuseFailAlloc_2939_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(
    mut v_type_2941_: *mut LeanObject,
    mut v_k_2942_: *mut LeanObject,
    mut v_cleanupAnnotations_2943_: *mut LeanObject,
    mut v_whnfType_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2950_: u8 = 0;
    let mut v_whnfType_boxed_2951_: u8 = 0;
    let mut v_res_2952_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2950_ = (lean_unbox(v_cleanupAnnotations_2943_) as u8);
    v_whnfType_boxed_2951_ = (lean_unbox(v_whnfType_2944_) as u8);
    v_res_2952_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_2941_, v_k_2942_, v_cleanupAnnotations_boxed_2950_, v_whnfType_boxed_2951_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
    lean_dec(v___y_2948_);
    lean_dec_ref(v___y_2947_);
    lean_dec(v___y_2946_);
    lean_dec_ref(v___y_2945_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(
    mut v_00_u03b1_2953_: *mut LeanObject,
    mut v_type_2954_: *mut LeanObject,
    mut v_k_2955_: *mut LeanObject,
    mut v_cleanupAnnotations_2956_: u8,
    mut v_whnfType_2957_: u8,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    v___x_2963_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v_type_2954_, v_k_2955_, v_cleanupAnnotations_2956_, v_whnfType_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
    return v___x_2963_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(
    mut v_00_u03b1_2964_: *mut LeanObject,
    mut v_type_2965_: *mut LeanObject,
    mut v_k_2966_: *mut LeanObject,
    mut v_cleanupAnnotations_2967_: *mut LeanObject,
    mut v_whnfType_2968_: *mut LeanObject,
    mut v___y_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2974_: u8 = 0;
    let mut v_whnfType_boxed_2975_: u8 = 0;
    let mut v_res_2976_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2974_ = (lean_unbox(v_cleanupAnnotations_2967_) as u8);
    v_whnfType_boxed_2975_ = (lean_unbox(v_whnfType_2968_) as u8);
    v_res_2976_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(v_00_u03b1_2964_, v_type_2965_, v_k_2966_, v_cleanupAnnotations_boxed_2974_, v_whnfType_boxed_2975_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
    lean_dec(v___y_2972_);
    lean_dec_ref(v___y_2971_);
    lean_dec(v___y_2970_);
    lean_dec_ref(v___y_2969_);
    return v_res_2976_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(
    mut v_msg_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
    mut v___y_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9957__overap_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    v___f_2984_ =
        l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0;
    v___x_9957__overap_2985_ = lean_panic_fn_borrowed(v___f_2984_, v_msg_2978_);
    lean_inc(v___y_2982_);
    lean_inc_ref(v___y_2981_);
    lean_inc(v___y_2980_);
    lean_inc_ref(v___y_2979_);
    v___x_2986_ = lean_apply_5(
        v___x_9957__overap_2985_,
        v___y_2979_,
        v___y_2980_,
        v___y_2981_,
        v___y_2982_,
        lean_box(0),
    );
    return v___x_2986_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(
    mut v_msg_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2993_: *mut LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(
        v_msg_2987_,
        v___y_2988_,
        v___y_2989_,
        v___y_2990_,
        v___y_2991_,
    );
    lean_dec(v___y_2991_);
    lean_dec_ref(v___y_2990_);
    lean_dec(v___y_2989_);
    lean_dec_ref(v___y_2988_);
    return v_res_2993_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(
    mut v_type_2994_: *mut LeanObject,
    mut v_maxFVars_x3f_2995_: *mut LeanObject,
    mut v_k_2996_: *mut LeanObject,
    mut v_cleanupAnnotations_2997_: u8,
    mut v_whnfType_2998_: u8,
    mut v___y_2999_: *mut LeanObject,
    mut v___y_3000_: *mut LeanObject,
    mut v___y_3001_: *mut LeanObject,
    mut v___y_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v_a_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3004_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3004_, 0, v_k_2996_);
                v___x_3005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_2994_,
                    v_maxFVars_x3f_2995_,
                    v___f_3004_,
                    v_cleanupAnnotations_2997_,
                    v_whnfType_2998_,
                    v___y_2999_,
                    v___y_3000_,
                    v___y_3001_,
                    v___y_3002_,
                );
                if lean_obj_tag(v___x_3005_) == 0 {
                    v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
                    v_isSharedCheck_3013_ = (!lean_is_exclusive(v___x_3005_)) as u8;
                    if v_isSharedCheck_3013_ == 0 {
                        v___x_3008_ = v___x_3005_;
                        v_isShared_3009_ = v_isSharedCheck_3013_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3006_);
                        lean_dec(v___x_3005_);
                        v___x_3008_ = lean_box(0);
                        v_isShared_3009_ = v_isSharedCheck_3013_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3014_ = lean_ctor_get(v___x_3005_, 0);
                    v_isSharedCheck_3021_ = (!lean_is_exclusive(v___x_3005_)) as u8;
                    if v_isSharedCheck_3021_ == 0 {
                        v___x_3016_ = v___x_3005_;
                        v_isShared_3017_ = v_isSharedCheck_3021_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3014_);
                        lean_dec(v___x_3005_);
                        v___x_3016_ = lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3021_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3009_ == 0 {
                    v___x_3011_ = v___x_3008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3011_;
            }
            3 => {
                if v_isShared_3017_ == 0 {
                    v___x_3019_ = v___x_3016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
                    v___x_3019_ = v_reuseFailAlloc_3020_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(
    mut v_type_3022_: *mut LeanObject,
    mut v_maxFVars_x3f_3023_: *mut LeanObject,
    mut v_k_3024_: *mut LeanObject,
    mut v_cleanupAnnotations_3025_: *mut LeanObject,
    mut v_whnfType_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
    mut v___y_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3032_: u8 = 0;
    let mut v_whnfType_boxed_3033_: u8 = 0;
    let mut v_res_3034_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3032_ = (lean_unbox(v_cleanupAnnotations_3025_) as u8);
    v_whnfType_boxed_3033_ = (lean_unbox(v_whnfType_3026_) as u8);
    v_res_3034_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_3022_, v_maxFVars_x3f_3023_, v_k_3024_, v_cleanupAnnotations_boxed_3032_, v_whnfType_boxed_3033_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
    lean_dec(v___y_3030_);
    lean_dec_ref(v___y_3029_);
    lean_dec(v___y_3028_);
    lean_dec_ref(v___y_3027_);
    return v_res_3034_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(
    mut v_00_u03b1_3035_: *mut LeanObject,
    mut v_type_3036_: *mut LeanObject,
    mut v_maxFVars_x3f_3037_: *mut LeanObject,
    mut v_k_3038_: *mut LeanObject,
    mut v_cleanupAnnotations_3039_: u8,
    mut v_whnfType_3040_: u8,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
    mut v___y_3044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    v___x_3046_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_type_3036_, v_maxFVars_x3f_3037_, v_k_3038_, v_cleanupAnnotations_3039_, v_whnfType_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
    return v___x_3046_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(
    mut v_00_u03b1_3047_: *mut LeanObject,
    mut v_type_3048_: *mut LeanObject,
    mut v_maxFVars_x3f_3049_: *mut LeanObject,
    mut v_k_3050_: *mut LeanObject,
    mut v_cleanupAnnotations_3051_: *mut LeanObject,
    mut v_whnfType_3052_: *mut LeanObject,
    mut v___y_3053_: *mut LeanObject,
    mut v___y_3054_: *mut LeanObject,
    mut v___y_3055_: *mut LeanObject,
    mut v___y_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3058_: u8 = 0;
    let mut v_whnfType_boxed_3059_: u8 = 0;
    let mut v_res_3060_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3058_ = (lean_unbox(v_cleanupAnnotations_3051_) as u8);
    v_whnfType_boxed_3059_ = (lean_unbox(v_whnfType_3052_) as u8);
    v_res_3060_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(v_00_u03b1_3047_, v_type_3048_, v_maxFVars_x3f_3049_, v_k_3050_, v_cleanupAnnotations_boxed_3058_, v_whnfType_boxed_3059_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
    lean_dec(v___y_3056_);
    lean_dec_ref(v___y_3055_);
    lean_dec(v___y_3054_);
    lean_dec_ref(v___y_3053_);
    return v_res_3060_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(
    mut v_upperBound_3061_: *mut LeanObject,
    mut v_val_3062_: *mut LeanObject,
    mut v___x_3063_: *mut LeanObject,
    mut v_fvars_3064_: *mut LeanObject,
    mut v___y_3065_: u8,
    mut v_a_3066_: *mut LeanObject,
    mut v_b_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
    mut v___y_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
    mut v___y_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u8 = 0;
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v_v_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3108_: u8 = 0;
    let mut v_hasFwdDeps_3109_: u8 = 0;
    let mut v_backDeps_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isProp_3111_: u8 = 0;
    let mut v_isDecInst_3112_: u8 = 0;
    let mut v_isInstance_3113_: u8 = 0;
    let mut v_dependsOnHigherOrderOutParam_3114_: u8 = 0;
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_a_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_a_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3140_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3078_ = lean_nat_dec_lt(v_a_3066_, v_upperBound_3061_);
                if v___x_3078_ == 0 {
                    lean_dec(v_a_3066_);
                    v___x_3079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3079_, 0, v_b_3067_);
                    return v___x_3079_;
                } else {
                    v_fst_3080_ = lean_ctor_get(v_b_3067_, 0);
                    v_snd_3081_ = lean_ctor_get(v_b_3067_, 1);
                    v_isSharedCheck_3144_ = (!lean_is_exclusive(v_b_3067_)) as u8;
                    if v_isSharedCheck_3144_ == 0 {
                        v___x_3083_ = v_b_3067_;
                        v_isShared_3084_ = v_isSharedCheck_3144_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3081_);
                        lean_inc(v_fst_3080_);
                        lean_dec(v_b_3067_);
                        v___x_3083_ = lean_box(0);
                        v_isShared_3084_ = v_isSharedCheck_3144_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3075_ = lean_unsigned_to_nat(1);
                v___x_3076_ = lean_nat_add(v_a_3066_, v___x_3075_);
                lean_dec(v_a_3066_);
                v_a_3066_ = v___x_3076_;
                v_b_3067_ = v_a_3074_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3085_ = l_Array_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__1(v_val_3062_, v_a_3066_);
                if v___x_3085_ == 0 {
                    if v_isShared_3084_ == 0 {
                        v___x_3087_ = v___x_3083_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_fst_3080_);
                        lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_snd_3081_);
                        v___x_3087_ = v_reuseFailAlloc_3088_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3089_ = lean_array_fget_borrowed(v___x_3063_, v_a_3066_);
                    v___x_3090_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(v_fvars_3064_, v___x_3089_);
                    if lean_obj_tag(v___x_3090_) == 1 {
                        v_val_3091_ = lean_ctor_get(v___x_3090_, 0);
                        lean_inc(v_val_3091_);
                        lean_dec_ref_known(v___x_3090_, 1);
                        lean_inc(v___y_3071_);
                        lean_inc_ref(v___y_3070_);
                        lean_inc(v___y_3069_);
                        lean_inc_ref(v___y_3068_);
                        lean_inc(v___x_3089_);
                        v___x_3092_ = lean_infer_type(
                            v___x_3089_,
                            v___y_3068_,
                            v___y_3069_,
                            v___y_3070_,
                            v___y_3071_,
                        );
                        if lean_obj_tag(v___x_3092_) == 0 {
                            v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
                            lean_inc(v_a_3093_);
                            lean_dec_ref_known(v___x_3092_, 1);
                            lean_inc(v___y_3071_);
                            lean_inc_ref(v___y_3070_);
                            lean_inc(v___y_3069_);
                            lean_inc_ref(v___y_3068_);
                            v___x_3094_ = lean_whnf(
                                v_a_3093_,
                                v___y_3068_,
                                v___y_3069_,
                                v___y_3070_,
                                v___y_3071_,
                            );
                            if lean_obj_tag(v___x_3094_) == 0 {
                                v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
                                lean_inc(v_a_3095_);
                                lean_dec_ref_known(v___x_3094_, 1);
                                v___x_3103_ = l_Lean_Expr_isForall(v_a_3095_);
                                lean_dec(v_a_3095_);
                                if v___x_3103_ == 0 {
                                    lean_dec(v_val_3091_);
                                    lean_del_object(v___x_3083_);
                                    v___x_3104_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3104_, 0, v_fst_3080_);
                                    lean_ctor_set(v___x_3104_, 1, v_snd_3081_);
                                    v_a_3074_ = v___x_3104_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3105_ = lean_array_get_size(v_fst_3080_);
                                    v___x_3106_ = lean_nat_dec_lt(v_val_3091_, v___x_3105_);
                                    if v___x_3106_ == 0 {
                                        lean_dec(v_val_3091_);
                                        v___y_3097_ = v_fst_3080_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_v_3107_ = lean_array_fget(v_fst_3080_, v_val_3091_);
                                        v_binderInfo_3108_ = lean_ctor_get_uint8(
                                            v_v_3107_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        );
                                        v_hasFwdDeps_3109_ = lean_ctor_get_uint8(
                                            v_v_3107_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1)
                                                as u32,
                                        );
                                        v_backDeps_3110_ = lean_ctor_get(v_v_3107_, 0);
                                        v_isProp_3111_ = lean_ctor_get_uint8(
                                            v_v_3107_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1 + 2)
                                                as u32,
                                        );
                                        v_isDecInst_3112_ = lean_ctor_get_uint8(
                                            v_v_3107_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1 + 3)
                                                as u32,
                                        );
                                        v_isInstance_3113_ = lean_ctor_get_uint8(
                                            v_v_3107_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1 + 4)
                                                as u32,
                                        );
                                        v_dependsOnHigherOrderOutParam_3114_ = lean_ctor_get_uint8(
                                            v_v_3107_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1 + 6)
                                                as u32,
                                        );
                                        v_isSharedCheck_3124_ =
                                            (!lean_is_exclusive(v_v_3107_)) as u8;
                                        if v_isSharedCheck_3124_ == 0 {
                                            v___x_3116_ = v_v_3107_;
                                            v_isShared_3117_ = v_isSharedCheck_3124_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_backDeps_3110_);
                                            lean_dec(v_v_3107_);
                                            v___x_3116_ = lean_box(0);
                                            v_isShared_3117_ = v_isSharedCheck_3124_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_val_3091_);
                                lean_del_object(v___x_3083_);
                                lean_dec(v_snd_3081_);
                                lean_dec(v_fst_3080_);
                                lean_dec(v_a_3066_);
                                v_a_3125_ = lean_ctor_get(v___x_3094_, 0);
                                v_isSharedCheck_3132_ = (!lean_is_exclusive(v___x_3094_)) as u8;
                                if v_isSharedCheck_3132_ == 0 {
                                    v___x_3127_ = v___x_3094_;
                                    v_isShared_3128_ = v_isSharedCheck_3132_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_3125_);
                                    lean_dec(v___x_3094_);
                                    v___x_3127_ = lean_box(0);
                                    v_isShared_3128_ = v_isSharedCheck_3132_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_3091_);
                            lean_del_object(v___x_3083_);
                            lean_dec(v_snd_3081_);
                            lean_dec(v_fst_3080_);
                            lean_dec(v_a_3066_);
                            v_a_3133_ = lean_ctor_get(v___x_3092_, 0);
                            v_isSharedCheck_3140_ = (!lean_is_exclusive(v___x_3092_)) as u8;
                            if v_isSharedCheck_3140_ == 0 {
                                v___x_3135_ = v___x_3092_;
                                v_isShared_3136_ = v_isSharedCheck_3140_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_3133_);
                                lean_dec(v___x_3092_);
                                v___x_3135_ = lean_box(0);
                                v_isShared_3136_ = v_isSharedCheck_3140_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3090_);
                        if v_isShared_3084_ == 0 {
                            v___x_3142_ = v___x_3083_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_fst_3080_);
                            lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_snd_3081_);
                            v___x_3142_ = v_reuseFailAlloc_3143_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_3074_ = v___x_3087_;
                state = 1;
                continue;
            }
            4 => {
                v___x_3098_ = l_Lean_Expr_fvarId_x21(v___x_3089_);
                v___x_3099_ = l_Lean_FVarIdSet_insert(v_snd_3081_, v___x_3098_);
                if v_isShared_3084_ == 0 {
                    lean_ctor_set(v___x_3083_, 1, v___x_3099_);
                    lean_ctor_set(v___x_3083_, 0, v___y_3097_);
                    v___x_3101_ = v___x_3083_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___y_3097_);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3099_);
                    v___x_3101_ = v_reuseFailAlloc_3102_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_3074_ = v___x_3101_;
                state = 1;
                continue;
            }
            6 => {
                v___x_3118_ = lean_box(0);
                v_xs_x27_3119_ = lean_array_fset(v_fst_3080_, v_val_3091_, v___x_3118_);
                if v_isShared_3117_ == 0 {
                    v___x_3121_ = v___x_3116_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, (7) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_backDeps_3110_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3123_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_binderInfo_3108_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3123_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_hasFwdDeps_3109_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3123_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_isProp_3111_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3123_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                        v_isDecInst_3112_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3123_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                        v_isInstance_3113_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3123_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 6) as u32,
                        v_dependsOnHigherOrderOutParam_3114_,
                    );
                    v___x_3121_ = v_reuseFailAlloc_3123_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_3121_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 5) as u32,
                    v___y_3065_,
                );
                v___x_3122_ = lean_array_fset(v_xs_x27_3119_, v_val_3091_, v___x_3121_);
                lean_dec(v_val_3091_);
                v___y_3097_ = v___x_3122_;
                state = 4;
                continue;
            }
            8 => {
                if v_isShared_3128_ == 0 {
                    v___x_3130_ = v___x_3127_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3130_;
            }
            10 => {
                if v_isShared_3136_ == 0 {
                    v___x_3138_ = v___x_3135_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
                    v___x_3138_ = v_reuseFailAlloc_3139_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3138_;
            }
            12 => {
                v_a_3074_ = v___x_3142_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg___boxed(
    mut v_upperBound_3145_: *mut LeanObject,
    mut v_val_3146_: *mut LeanObject,
    mut v___x_3147_: *mut LeanObject,
    mut v_fvars_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v_a_3150_: *mut LeanObject,
    mut v_b_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
    mut v___y_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_12426__boxed_3157_: u8 = 0;
    let mut v_res_3158_: *mut LeanObject = core::ptr::null_mut();
    v___y_12426__boxed_3157_ = (lean_unbox(v___y_3149_) as u8);
    v_res_3158_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_3145_, v_val_3146_, v___x_3147_, v_fvars_3148_, v___y_12426__boxed_3157_, v_a_3150_, v_b_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
    lean_dec(v___y_3155_);
    lean_dec_ref(v___y_3154_);
    lean_dec(v___y_3153_);
    lean_dec_ref(v___y_3152_);
    lean_dec_ref(v_fvars_3148_);
    lean_dec_ref(v___x_3147_);
    lean_dec_ref(v_val_3146_);
    lean_dec(v_upperBound_3145_);
    return v_res_3158_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(
    mut v_x_3162_: *mut LeanObject,
    mut v_type_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u8 = 0;
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    v___x_3169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___closed__1;
    v___x_3170_ = l_Lean_Expr_isAppOf(v_type_3163_, v___x_3169_);
    v___x_3171_ = lean_box((v___x_3170_) as usize);
    v___x_3172_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3172_, 0, v___x_3171_);
    return v___x_3172_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0___boxed(
    mut v_x_3173_: *mut LeanObject,
    mut v_type_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3180_: *mut LeanObject = core::ptr::null_mut();
    v_res_3180_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__0(v_x_3173_, v_type_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
    lean_dec(v___y_3178_);
    lean_dec_ref(v___y_3177_);
    lean_dec(v___y_3176_);
    lean_dec_ref(v___y_3175_);
    lean_dec_ref(v_type_3174_);
    lean_dec_ref(v_x_3173_);
    return v_res_3180_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(
    mut v_k_3181_: *mut LeanObject,
    mut v_t_3182_: *mut LeanObject,
) -> u8 {
    let mut v_k_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3182_) == 0 {
                    v_k_3183_ = lean_ctor_get(v_t_3182_, 1);
                    v_l_3184_ = lean_ctor_get(v_t_3182_, 3);
                    v_r_3185_ = lean_ctor_get(v_t_3182_, 4);
                    v___x_3186_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3181_, v_k_3183_);
                    match v___x_3186_ {
                        0 => {
                            v_t_3182_ = v_l_3184_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_3188_ = 1;
                            return v___x_3188_;
                        }
                        _ => {
                            v_t_3182_ = v_r_3185_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_3190_ = 0;
                    return v___x_3190_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(
    mut v_k_3191_: *mut LeanObject,
    mut v_t_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3193_: u8 = 0;
    let mut v_r_3194_: *mut LeanObject = core::ptr::null_mut();
    v_res_3193_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_3191_, v_t_3192_);
    lean_dec(v_t_3192_);
    lean_dec(v_k_3191_);
    v_r_3194_ = lean_box((v_res_3193_) as usize);
    return v_r_3194_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(
    mut v_snd_3195_: *mut LeanObject,
    mut v_e_3196_: *mut LeanObject,
) -> u8 {
    let mut v___x_3197_: u8 = 0;
    v___x_3197_ = l_Lean_Expr_isFVar(v_e_3196_);
    if v___x_3197_ == 0 {
        return v___x_3197_;
    } else {
        let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3199_: u8 = 0;
        v___x_3198_ = l_Lean_Expr_fvarId_x21(v_e_3196_);
        v___x_3199_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v___x_3198_, v_snd_3195_);
        lean_dec(v___x_3198_);
        return v___x_3199_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed(
    mut v_snd_3200_: *mut LeanObject,
    mut v_e_3201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3202_: u8 = 0;
    let mut v_r_3203_: *mut LeanObject = core::ptr::null_mut();
    v_res_3202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1(v_snd_3200_, v_e_3201_);
    lean_dec_ref(v_e_3201_);
    lean_dec(v_snd_3200_);
    v_r_3203_ = lean_box((v_res_3202_) as usize);
    return v_r_3203_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3206_: *mut LeanObject = core::ptr::null_mut();
    v___x_3205_ = lean_box(0);
    v_dummy_3206_ = l_Lean_Expr_sort___override(v___x_3205_);
    return v_dummy_3206_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    v___x_3210_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4;
    v___x_3211_ = lean_unsigned_to_nat(47);
    v___x_3212_ = lean_unsigned_to_nat(121);
    v___x_3213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__3;
    v___x_3214_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__2;
    v___x_3215_ = l_mkPanicMessageWithDecl(
        v___x_3214_,
        v___x_3213_,
        v___x_3212_,
        v___x_3211_,
        v___x_3210_,
    );
    return v___x_3215_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(
    mut v_upperBound_3216_: *mut LeanObject,
    mut v_fvars_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_b_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: u8 = 0;
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3239_: u8 = 0;
    let mut v___f_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3245_: u8 = 0;
    let mut v___y_3246_: u8 = 0;
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: u8 = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v_dummy_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v_reuseFailAlloc_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v_a_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3316_: u8 = 0;
    let mut v_a_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3324_: u8 = 0;
    let mut v___y_3326_: u8 = 0;
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: u8 = 0;
    let mut v_a_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v___f_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: u8 = 0;
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut v_a_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3349_: u8 = 0;
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3230_ = lean_nat_dec_lt(v_a_3218_, v_upperBound_3216_);
                if v___x_3230_ == 0 {
                    lean_dec(v_a_3218_);
                    v___x_3231_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3231_, 0, v_b_3219_);
                    return v___x_3231_;
                } else {
                    v___x_3232_ = lean_array_fget_borrowed(v_fvars_3217_, v_a_3218_);
                    v___x_3233_ = l_Lean_Meta_getFVarLocalDecl___redArg(
                        v___x_3232_,
                        v___y_3220_,
                        v___y_3222_,
                        v___y_3223_,
                    );
                    if lean_obj_tag(v___x_3233_) == 0 {
                        v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
                        lean_inc(v_a_3234_);
                        lean_dec_ref_known(v___x_3233_, 1);
                        v_fst_3235_ = lean_ctor_get(v_b_3219_, 0);
                        v_snd_3236_ = lean_ctor_get(v_b_3219_, 1);
                        v_isSharedCheck_3345_ = (!lean_is_exclusive(v_b_3219_)) as u8;
                        if v_isSharedCheck_3345_ == 0 {
                            v___x_3238_ = v_b_3219_;
                            v_isShared_3239_ = v_isSharedCheck_3345_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_3236_);
                            lean_inc(v_fst_3235_);
                            lean_dec(v_b_3219_);
                            v___x_3238_ = lean_box(0);
                            v_isShared_3239_ = v_isSharedCheck_3345_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_3219_);
                        lean_dec(v_a_3218_);
                        v_a_3346_ = lean_ctor_get(v___x_3233_, 0);
                        v_isSharedCheck_3353_ = (!lean_is_exclusive(v___x_3233_)) as u8;
                        if v_isSharedCheck_3353_ == 0 {
                            v___x_3348_ = v___x_3233_;
                            v_isShared_3349_ = v_isSharedCheck_3353_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_3346_);
                            lean_dec(v___x_3233_);
                            v___x_3348_ = lean_box(0);
                            v_isShared_3349_ = v_isSharedCheck_3353_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3227_ = lean_unsigned_to_nat(1);
                v___x_3228_ = lean_nat_add(v_a_3218_, v___x_3227_);
                lean_dec(v_a_3218_);
                v_a_3218_ = v___x_3228_;
                v_b_3219_ = v_a_3226_;
                state = 0;
                continue;
            }
            2 => {
                v___f_3240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__0;
                v___x_3241_ = l_Lean_LocalDecl_type(v_a_3234_);
                v___x_3242_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(
                    v_fvars_3217_,
                    v___x_3241_,
                );
                if lean_obj_tag(v_snd_3236_) == 0 {
                    lean_inc_ref(v_snd_3236_);
                    v___f_3341_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_3341_, 0, v_snd_3236_);
                    v___x_3342_ = lean_find_expr(v___f_3341_, v___x_3241_);
                    lean_dec_ref(v___f_3341_);
                    if lean_obj_tag(v___x_3342_) == 0 {
                        v___x_3343_ = 0;
                        v___y_3326_ = v___x_3343_;
                        state = 17;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_3342_, 1);
                        v___y_3326_ = v___x_3230_;
                        state = 17;
                        continue;
                    }
                } else {
                    v___x_3344_ = 0;
                    v___y_3326_ = v___x_3344_;
                    state = 17;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3241_);
                v___x_3247_ = l_Lean_Meta_isProp(
                    v___x_3241_,
                    v___y_3220_,
                    v___y_3221_,
                    v___y_3222_,
                    v___y_3223_,
                );
                if lean_obj_tag(v___x_3247_) == 0 {
                    v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
                    lean_inc(v_a_3248_);
                    lean_dec_ref_known(v___x_3247_, 1);
                    v___x_3249_ = 0;
                    lean_inc_ref(v___x_3241_);
                    v___x_3250_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(v___x_3241_, v___f_3240_, v___x_3249_, v___x_3249_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
                    if lean_obj_tag(v___x_3250_) == 0 {
                        v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
                        lean_inc(v_a_3251_);
                        lean_dec_ref_known(v___x_3250_, 1);
                        v___x_3252_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(
                            v_fst_3235_,
                            v___x_3242_,
                        );
                        lean_dec(v_fst_3235_);
                        v___x_3253_ = l_Lean_LocalDecl_binderInfo(v_a_3234_);
                        lean_dec(v_a_3234_);
                        v___x_3254_ = lean_alloc_ctor(0, 1, (7) as u32);
                        lean_ctor_set(v___x_3254_, 0, v___x_3242_);
                        lean_ctor_set_uint8(
                            v___x_3254_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_3253_,
                        );
                        lean_ctor_set_uint8(
                            v___x_3254_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            v___x_3249_,
                        );
                        v___x_3255_ = (lean_unbox(v_a_3248_) as u8);
                        lean_dec(v_a_3248_);
                        lean_ctor_set_uint8(
                            v___x_3254_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                            v___x_3255_,
                        );
                        v___x_3256_ = (lean_unbox(v_a_3251_) as u8);
                        lean_dec(v_a_3251_);
                        lean_ctor_set_uint8(
                            v___x_3254_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                            v___x_3256_,
                        );
                        lean_ctor_set_uint8(
                            v___x_3254_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                            v___y_3246_,
                        );
                        lean_ctor_set_uint8(
                            v___x_3254_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 5) as u32,
                            v___x_3249_,
                        );
                        lean_ctor_set_uint8(
                            v___x_3254_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 6) as u32,
                            v___y_3245_,
                        );
                        v___x_3257_ = lean_array_push(v___x_3252_, v___x_3254_);
                        if v___y_3246_ == 0 {
                            lean_dec(v___y_3244_);
                            lean_dec_ref(v___x_3241_);
                            if v_isShared_3239_ == 0 {
                                lean_ctor_set(v___x_3238_, 0, v___x_3257_);
                                v___x_3259_ = v___x_3238_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
                                lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_snd_3236_);
                                v___x_3259_ = v_reuseFailAlloc_3260_;
                                state = 4;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___y_3244_) == 1 {
                                v_val_3261_ = lean_ctor_get(v___y_3244_, 0);
                                lean_inc(v_val_3261_);
                                lean_dec_ref_known(v___y_3244_, 1);
                                v___x_3262_ = lean_st_ref_get(v___y_3223_);
                                v_env_3263_ = lean_ctor_get(v___x_3262_, 0);
                                lean_inc_ref(v_env_3263_);
                                lean_dec(v___x_3262_);
                                v___x_3264_ =
                                    l_Lean_getOutParamPositions_x3f(v_env_3263_, v_val_3261_);
                                lean_dec(v_val_3261_);
                                if lean_obj_tag(v___x_3264_) == 1 {
                                    v_val_3265_ = lean_ctor_get(v___x_3264_, 0);
                                    lean_inc(v_val_3265_);
                                    lean_dec_ref_known(v___x_3264_, 1);
                                    v___x_3266_ = lean_array_get_size(v_val_3265_);
                                    v___x_3267_ = lean_unsigned_to_nat(0);
                                    v___x_3268_ = lean_nat_dec_eq(v___x_3266_, v___x_3267_);
                                    if v___x_3268_ == 0 {
                                        v_dummy_3269_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__1);
                                        v_nargs_3270_ = l_Lean_Expr_getAppNumArgs(v___x_3241_);
                                        lean_inc(v_nargs_3270_);
                                        v___x_3271_ = lean_mk_array(v_nargs_3270_, v_dummy_3269_);
                                        v___x_3272_ = lean_unsigned_to_nat(1);
                                        v___x_3273_ = lean_nat_sub(v_nargs_3270_, v___x_3272_);
                                        lean_dec(v_nargs_3270_);
                                        v___x_3274_ =
                                            l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                                v___x_3241_,
                                                v___x_3271_,
                                                v___x_3273_,
                                            );
                                        v___x_3275_ = lean_array_get_size(v___x_3274_);
                                        if v_isShared_3239_ == 0 {
                                            lean_ctor_set(v___x_3238_, 0, v___x_3257_);
                                            v___x_3277_ = v___x_3238_;
                                            state = 5;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3289_ =
                                                lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3257_);
                                            lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_snd_3236_);
                                            v___x_3277_ = v_reuseFailAlloc_3289_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_val_3265_);
                                        lean_dec_ref(v___x_3241_);
                                        if v_isShared_3239_ == 0 {
                                            lean_ctor_set(v___x_3238_, 0, v___x_3257_);
                                            v___x_3291_ = v___x_3238_;
                                            state = 8;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3292_ =
                                                lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3257_);
                                            lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_snd_3236_);
                                            v___x_3291_ = v_reuseFailAlloc_3292_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v___x_3264_);
                                    lean_dec_ref(v___x_3241_);
                                    if v_isShared_3239_ == 0 {
                                        lean_ctor_set(v___x_3238_, 0, v___x_3257_);
                                        v___x_3294_ = v___x_3238_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3257_);
                                        lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_snd_3236_);
                                        v___x_3294_ = v_reuseFailAlloc_3295_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___y_3244_);
                                lean_dec_ref(v___x_3241_);
                                v___x_3296_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__5);
                                v___x_3297_ = l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(v___x_3296_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
                                if lean_obj_tag(v___x_3297_) == 0 {
                                    lean_dec_ref_known(v___x_3297_, 1);
                                    if v_isShared_3239_ == 0 {
                                        lean_ctor_set(v___x_3238_, 0, v___x_3257_);
                                        v___x_3299_ = v___x_3238_;
                                        state = 10;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3257_);
                                        lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_snd_3236_);
                                        v___x_3299_ = v_reuseFailAlloc_3300_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v___x_3257_);
                                    lean_del_object(v___x_3238_);
                                    lean_dec(v_snd_3236_);
                                    lean_dec(v_a_3218_);
                                    v_a_3301_ = lean_ctor_get(v___x_3297_, 0);
                                    v_isSharedCheck_3308_ = (!lean_is_exclusive(v___x_3297_)) as u8;
                                    if v_isSharedCheck_3308_ == 0 {
                                        v___x_3303_ = v___x_3297_;
                                        v_isShared_3304_ = v_isSharedCheck_3308_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3301_);
                                        lean_dec(v___x_3297_);
                                        v___x_3303_ = lean_box(0);
                                        v_isShared_3304_ = v_isSharedCheck_3308_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_3248_);
                        lean_dec(v___y_3244_);
                        lean_dec_ref(v___x_3242_);
                        lean_dec_ref(v___x_3241_);
                        lean_del_object(v___x_3238_);
                        lean_dec(v_snd_3236_);
                        lean_dec(v_fst_3235_);
                        lean_dec(v_a_3234_);
                        lean_dec(v_a_3218_);
                        v_a_3309_ = lean_ctor_get(v___x_3250_, 0);
                        v_isSharedCheck_3316_ = (!lean_is_exclusive(v___x_3250_)) as u8;
                        if v_isSharedCheck_3316_ == 0 {
                            v___x_3311_ = v___x_3250_;
                            v_isShared_3312_ = v_isSharedCheck_3316_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3309_);
                            lean_dec(v___x_3250_);
                            v___x_3311_ = lean_box(0);
                            v_isShared_3312_ = v_isSharedCheck_3316_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3244_);
                    lean_dec_ref(v___x_3242_);
                    lean_dec_ref(v___x_3241_);
                    lean_del_object(v___x_3238_);
                    lean_dec(v_snd_3236_);
                    lean_dec(v_fst_3235_);
                    lean_dec(v_a_3234_);
                    lean_dec(v_a_3218_);
                    v_a_3317_ = lean_ctor_get(v___x_3247_, 0);
                    v_isSharedCheck_3324_ = (!lean_is_exclusive(v___x_3247_)) as u8;
                    if v_isSharedCheck_3324_ == 0 {
                        v___x_3319_ = v___x_3247_;
                        v_isShared_3320_ = v_isSharedCheck_3324_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3317_);
                        lean_dec(v___x_3247_);
                        v___x_3319_ = lean_box(0);
                        v_isShared_3320_ = v_isSharedCheck_3324_;
                        state = 15;
                        continue;
                    }
                }
            }
            4 => {
                v_a_3226_ = v___x_3259_;
                state = 1;
                continue;
            }
            5 => {
                v___x_3278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v___x_3275_, v_val_3265_, v___x_3274_, v_fvars_3217_, v___y_3246_, v___x_3267_, v___x_3277_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
                lean_dec_ref(v___x_3274_);
                lean_dec(v_val_3265_);
                if lean_obj_tag(v___x_3278_) == 0 {
                    v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
                    lean_inc(v_a_3279_);
                    lean_dec_ref_known(v___x_3278_, 1);
                    v_fst_3280_ = lean_ctor_get(v_a_3279_, 0);
                    v_snd_3281_ = lean_ctor_get(v_a_3279_, 1);
                    v_isSharedCheck_3288_ = (!lean_is_exclusive(v_a_3279_)) as u8;
                    if v_isSharedCheck_3288_ == 0 {
                        v___x_3283_ = v_a_3279_;
                        v_isShared_3284_ = v_isSharedCheck_3288_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_3281_);
                        lean_inc(v_fst_3280_);
                        lean_dec(v_a_3279_);
                        v___x_3283_ = lean_box(0);
                        v_isShared_3284_ = v_isSharedCheck_3288_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3218_);
                    return v___x_3278_;
                }
            }
            6 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_fst_3280_);
                    lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_snd_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_3226_ = v___x_3286_;
                state = 1;
                continue;
            }
            8 => {
                v_a_3226_ = v___x_3291_;
                state = 1;
                continue;
            }
            9 => {
                v_a_3226_ = v___x_3294_;
                state = 1;
                continue;
            }
            10 => {
                v_a_3226_ = v___x_3299_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_3304_ == 0 {
                    v___x_3306_ = v___x_3303_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3306_;
            }
            13 => {
                if v_isShared_3312_ == 0 {
                    v___x_3314_ = v___x_3311_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
                    v___x_3314_ = v_reuseFailAlloc_3315_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3314_;
            }
            15 => {
                if v_isShared_3320_ == 0 {
                    v___x_3322_ = v___x_3319_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
                    v___x_3322_ = v_reuseFailAlloc_3323_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3322_;
            }
            17 => {
                lean_inc_ref(v___x_3241_);
                v___x_3327_ = l_Lean_Meta_isClass_x3f(
                    v___x_3241_,
                    v___y_3220_,
                    v___y_3221_,
                    v___y_3222_,
                    v___y_3223_,
                );
                if lean_obj_tag(v___x_3327_) == 0 {
                    v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
                    lean_inc(v_a_3328_);
                    lean_dec_ref_known(v___x_3327_, 1);
                    if lean_obj_tag(v_a_3328_) == 0 {
                        v___x_3329_ = 0;
                        v___y_3244_ = v_a_3328_;
                        v___y_3245_ = v___y_3326_;
                        v___y_3246_ = v___x_3329_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3330_ = l_Lean_LocalDecl_binderInfo(v_a_3234_);
                        v___x_3331_ = l_Lean_BinderInfo_isExplicit(v___x_3330_);
                        if v___x_3331_ == 0 {
                            v___y_3244_ = v_a_3328_;
                            v___y_3245_ = v___y_3326_;
                            v___y_3246_ = v___x_3230_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3332_ = 0;
                            v___y_3244_ = v_a_3328_;
                            v___y_3245_ = v___y_3326_;
                            v___y_3246_ = v___x_3332_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3242_);
                    lean_dec_ref(v___x_3241_);
                    lean_del_object(v___x_3238_);
                    lean_dec(v_snd_3236_);
                    lean_dec(v_fst_3235_);
                    lean_dec(v_a_3234_);
                    lean_dec(v_a_3218_);
                    v_a_3333_ = lean_ctor_get(v___x_3327_, 0);
                    v_isSharedCheck_3340_ = (!lean_is_exclusive(v___x_3327_)) as u8;
                    if v_isSharedCheck_3340_ == 0 {
                        v___x_3335_ = v___x_3327_;
                        v_isShared_3336_ = v_isSharedCheck_3340_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_3333_);
                        lean_dec(v___x_3327_);
                        v___x_3335_ = lean_box(0);
                        v_isShared_3336_ = v_isSharedCheck_3340_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_3336_ == 0 {
                    v___x_3338_ = v___x_3335_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
                    v___x_3338_ = v_reuseFailAlloc_3339_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3338_;
            }
            20 => {
                if v_isShared_3349_ == 0 {
                    v___x_3351_ = v___x_3348_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
                    v___x_3351_ = v_reuseFailAlloc_3352_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___boxed(
    mut v_upperBound_3354_: *mut LeanObject,
    mut v_fvars_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_b_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
    mut v___y_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3363_: *mut LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_3354_, v_fvars_3355_, v_a_3356_, v_b_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
    lean_dec(v___y_3361_);
    lean_dec_ref(v___y_3360_);
    lean_dec(v___y_3359_);
    lean_dec_ref(v___y_3358_);
    lean_dec_ref(v_fvars_3355_);
    lean_dec(v_upperBound_3354_);
    return v_res_3363_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(
    mut v___x_3366_: *mut LeanObject,
    mut v_fvars_3367_: *mut LeanObject,
    mut v_type_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v_fst_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3386_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut v_unused_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut v_a_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3374_ = lean_array_get_size(v_fvars_3367_);
                v___x_3375_ = lean_unsigned_to_nat(0);
                v___x_3376_ =
                    l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___closed__0;
                v___x_3377_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3377_, 0, v___x_3376_);
                lean_ctor_set(v___x_3377_, 1, v___x_3366_);
                v___x_3378_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v___x_3374_, v_fvars_3367_, v___x_3375_, v___x_3377_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
                if lean_obj_tag(v___x_3378_) == 0 {
                    v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
                    v_isSharedCheck_3397_ = (!lean_is_exclusive(v___x_3378_)) as u8;
                    if v_isSharedCheck_3397_ == 0 {
                        v___x_3381_ = v___x_3378_;
                        v_isShared_3382_ = v_isSharedCheck_3397_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3379_);
                        lean_dec(v___x_3378_);
                        v___x_3381_ = lean_box(0);
                        v_isShared_3382_ = v_isSharedCheck_3397_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3398_ = lean_ctor_get(v___x_3378_, 0);
                    v_isSharedCheck_3405_ = (!lean_is_exclusive(v___x_3378_)) as u8;
                    if v_isSharedCheck_3405_ == 0 {
                        v___x_3400_ = v___x_3378_;
                        v_isShared_3401_ = v_isSharedCheck_3405_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3398_);
                        lean_dec(v___x_3378_);
                        v___x_3400_ = lean_box(0);
                        v_isShared_3401_ = v_isSharedCheck_3405_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3383_ = lean_ctor_get(v_a_3379_, 0);
                v_isSharedCheck_3395_ = (!lean_is_exclusive(v_a_3379_)) as u8;
                if v_isSharedCheck_3395_ == 0 {
                    v_unused_3396_ = lean_ctor_get(v_a_3379_, 1);
                    lean_dec(v_unused_3396_);
                    v___x_3385_ = v_a_3379_;
                    v_isShared_3386_ = v_isSharedCheck_3395_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_3383_);
                    lean_dec(v_a_3379_);
                    v___x_3385_ = lean_box(0);
                    v_isShared_3386_ = v_isSharedCheck_3395_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3387_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(
                    v_fvars_3367_,
                    v_type_3368_,
                );
                v___x_3388_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(
                    v_fst_3383_,
                    v___x_3387_,
                );
                lean_dec(v_fst_3383_);
                if v_isShared_3386_ == 0 {
                    lean_ctor_set(v___x_3385_, 1, v___x_3387_);
                    lean_ctor_set(v___x_3385_, 0, v___x_3388_);
                    v___x_3390_ = v___x_3385_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3388_);
                    lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3387_);
                    v___x_3390_ = v_reuseFailAlloc_3394_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3382_ == 0 {
                    lean_ctor_set(v___x_3381_, 0, v___x_3390_);
                    v___x_3392_ = v___x_3381_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
                    v___x_3392_ = v_reuseFailAlloc_3393_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3392_;
            }
            5 => {
                if v_isShared_3401_ == 0 {
                    v___x_3403_ = v___x_3400_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
                    v___x_3403_ = v_reuseFailAlloc_3404_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(
    mut v___x_3406_: *mut LeanObject,
    mut v_fvars_3407_: *mut LeanObject,
    mut v_type_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3414_: *mut LeanObject = core::ptr::null_mut();
    v_res_3414_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(
        v___x_3406_,
        v_fvars_3407_,
        v_type_3408_,
        v___y_3409_,
        v___y_3410_,
        v___y_3411_,
        v___y_3412_,
    );
    lean_dec(v___y_3412_);
    lean_dec_ref(v___y_3411_);
    lean_dec(v___y_3410_);
    lean_dec_ref(v___y_3409_);
    lean_dec_ref(v_type_3408_);
    lean_dec_ref(v_fvars_3407_);
    return v_res_3414_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(
    mut v_fn_3415_: *mut LeanObject,
    mut v_maxArgs_x3f_3416_: *mut LeanObject,
    mut v___f_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_3426_: u8 = 0;
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: u8 = 0;
    let mut v___y_3430_: u8 = 0;
    let mut v_foApprox_3431_: u8 = 0;
    let mut v_ctxApprox_3432_: u8 = 0;
    let mut v_quasiPatternApprox_3433_: u8 = 0;
    let mut v_constApprox_3434_: u8 = 0;
    let mut v_isDefEqStuckEx_3435_: u8 = 0;
    let mut v_unificationHints_3436_: u8 = 0;
    let mut v_proofIrrelevance_3437_: u8 = 0;
    let mut v_assignSyntheticOpaque_3438_: u8 = 0;
    let mut v_offsetCnstrs_3439_: u8 = 0;
    let mut v_etaStruct_3440_: u8 = 0;
    let mut v_univApprox_3441_: u8 = 0;
    let mut v_iota_3442_: u8 = 0;
    let mut v_beta_3443_: u8 = 0;
    let mut v_proj_3444_: u8 = 0;
    let mut v_zeta_3445_: u8 = 0;
    let mut v_zetaDelta_3446_: u8 = 0;
    let mut v_zetaUnused_3447_: u8 = 0;
    let mut v_zetaHave_3448_: u8 = 0;
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v_trackZetaDelta_3452_: u8 = 0;
    let mut v_zetaDeltaSet_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3459_: u8 = 0;
    let mut v_inTypeClassResolution_3460_: u8 = 0;
    let mut v_cacheInferType_3461_: u8 = 0;
    let mut v_config_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u64 = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: u64 = 0;
    let mut v___x_3469_: u64 = 0;
    let mut v___x_3470_: u64 = 0;
    let mut v___x_3471_: u64 = 0;
    let mut v_key_3472_: u64 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v_unused_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3487_: u8 = 0;
    let mut v___x_3488_: u8 = 0;
    let mut v_a_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3421_);
                lean_inc_ref(v___y_3420_);
                lean_inc(v___y_3419_);
                lean_inc_ref(v___y_3418_);
                v___x_3423_ = lean_infer_type(
                    v_fn_3415_,
                    v___y_3418_,
                    v___y_3419_,
                    v___y_3420_,
                    v___y_3421_,
                );
                if lean_obj_tag(v___x_3423_) == 0 {
                    v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
                    lean_inc(v_a_3424_);
                    lean_dec_ref_known(v___x_3423_, 1);
                    v___x_3425_ = l_Lean_Meta_Context_config(v___y_3418_);
                    v_transparency_3426_ = lean_ctor_get_uint8(v___x_3425_, 9 as u32);
                    v___x_3427_ = 1;
                    v___x_3428_ = 0;
                    v___x_3488_ =
                        l_Lean_Meta_TransparencyMode_lt(v_transparency_3426_, v___x_3427_);
                    if v___x_3488_ == 0 {
                        v___y_3430_ = v_transparency_3426_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3430_ = v___x_3427_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_3421_);
                    lean_dec_ref(v___y_3420_);
                    lean_dec(v___y_3419_);
                    lean_dec_ref(v___y_3418_);
                    lean_dec_ref(v___f_3417_);
                    lean_dec(v_maxArgs_x3f_3416_);
                    v_a_3489_ = lean_ctor_get(v___x_3423_, 0);
                    v_isSharedCheck_3496_ = (!lean_is_exclusive(v___x_3423_)) as u8;
                    if v_isSharedCheck_3496_ == 0 {
                        v___x_3491_ = v___x_3423_;
                        v_isShared_3492_ = v_isSharedCheck_3496_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3489_);
                        lean_dec(v___x_3423_);
                        v___x_3491_ = lean_box(0);
                        v_isShared_3492_ = v_isSharedCheck_3496_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_foApprox_3431_ = lean_ctor_get_uint8(v___x_3425_, 0 as u32);
                v_ctxApprox_3432_ = lean_ctor_get_uint8(v___x_3425_, 1 as u32);
                v_quasiPatternApprox_3433_ = lean_ctor_get_uint8(v___x_3425_, 2 as u32);
                v_constApprox_3434_ = lean_ctor_get_uint8(v___x_3425_, 3 as u32);
                v_isDefEqStuckEx_3435_ = lean_ctor_get_uint8(v___x_3425_, 4 as u32);
                v_unificationHints_3436_ = lean_ctor_get_uint8(v___x_3425_, 5 as u32);
                v_proofIrrelevance_3437_ = lean_ctor_get_uint8(v___x_3425_, 6 as u32);
                v_assignSyntheticOpaque_3438_ = lean_ctor_get_uint8(v___x_3425_, 7 as u32);
                v_offsetCnstrs_3439_ = lean_ctor_get_uint8(v___x_3425_, 8 as u32);
                v_etaStruct_3440_ = lean_ctor_get_uint8(v___x_3425_, 10 as u32);
                v_univApprox_3441_ = lean_ctor_get_uint8(v___x_3425_, 11 as u32);
                v_iota_3442_ = lean_ctor_get_uint8(v___x_3425_, 12 as u32);
                v_beta_3443_ = lean_ctor_get_uint8(v___x_3425_, 13 as u32);
                v_proj_3444_ = lean_ctor_get_uint8(v___x_3425_, 14 as u32);
                v_zeta_3445_ = lean_ctor_get_uint8(v___x_3425_, 15 as u32);
                v_zetaDelta_3446_ = lean_ctor_get_uint8(v___x_3425_, 16 as u32);
                v_zetaUnused_3447_ = lean_ctor_get_uint8(v___x_3425_, 17 as u32);
                v_zetaHave_3448_ = lean_ctor_get_uint8(v___x_3425_, 18 as u32);
                v_isSharedCheck_3487_ = (!lean_is_exclusive(v___x_3425_)) as u8;
                if v_isSharedCheck_3487_ == 0 {
                    v___x_3450_ = v___x_3425_;
                    v_isShared_3451_ = v_isSharedCheck_3487_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_3425_);
                    v___x_3450_ = lean_box(0);
                    v_isShared_3451_ = v_isSharedCheck_3487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_3452_ = lean_ctor_get_uint8(
                    v___y_3418_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3453_ = lean_ctor_get(v___y_3418_, 1);
                lean_inc(v_zetaDeltaSet_3453_);
                v_lctx_3454_ = lean_ctor_get(v___y_3418_, 2);
                lean_inc_ref(v_lctx_3454_);
                v_localInstances_3455_ = lean_ctor_get(v___y_3418_, 3);
                lean_inc_ref(v_localInstances_3455_);
                v_defEqCtx_x3f_3456_ = lean_ctor_get(v___y_3418_, 4);
                lean_inc(v_defEqCtx_x3f_3456_);
                v_synthPendingDepth_3457_ = lean_ctor_get(v___y_3418_, 5);
                lean_inc(v_synthPendingDepth_3457_);
                v_canUnfold_x3f_3458_ = lean_ctor_get(v___y_3418_, 6);
                lean_inc(v_canUnfold_x3f_3458_);
                v_univApprox_3459_ = lean_ctor_get_uint8(
                    v___y_3418_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3460_ = lean_ctor_get_uint8(
                    v___y_3418_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3461_ = lean_ctor_get_uint8(
                    v___y_3418_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_3451_ == 0 {
                    v_config_3463_ = v___x_3450_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 0 as u32, v_foApprox_3431_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 1 as u32, v_ctxApprox_3432_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3486_,
                        2 as u32,
                        v_quasiPatternApprox_3433_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 3 as u32, v_constApprox_3434_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 4 as u32, v_isDefEqStuckEx_3435_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 5 as u32, v_unificationHints_3436_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 6 as u32, v_proofIrrelevance_3437_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3486_,
                        7 as u32,
                        v_assignSyntheticOpaque_3438_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 8 as u32, v_offsetCnstrs_3439_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 10 as u32, v_etaStruct_3440_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 11 as u32, v_univApprox_3441_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 12 as u32, v_iota_3442_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 13 as u32, v_beta_3443_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 14 as u32, v_proj_3444_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 15 as u32, v_zeta_3445_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 16 as u32, v_zetaDelta_3446_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 17 as u32, v_zetaUnused_3447_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 18 as u32, v_zetaHave_3448_);
                    v_config_3463_ = v_reuseFailAlloc_3486_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_3463_, 9 as u32, v___y_3430_);
                v___x_3464_ = l_Lean_Meta_Context_configKey(v___y_3418_);
                v_isSharedCheck_3478_ = (!lean_is_exclusive(v___y_3418_)) as u8;
                if v_isSharedCheck_3478_ == 0 {
                    v_unused_3479_ = lean_ctor_get(v___y_3418_, 6);
                    lean_dec(v_unused_3479_);
                    v_unused_3480_ = lean_ctor_get(v___y_3418_, 5);
                    lean_dec(v_unused_3480_);
                    v_unused_3481_ = lean_ctor_get(v___y_3418_, 4);
                    lean_dec(v_unused_3481_);
                    v_unused_3482_ = lean_ctor_get(v___y_3418_, 3);
                    lean_dec(v_unused_3482_);
                    v_unused_3483_ = lean_ctor_get(v___y_3418_, 2);
                    lean_dec(v_unused_3483_);
                    v_unused_3484_ = lean_ctor_get(v___y_3418_, 1);
                    lean_dec(v_unused_3484_);
                    v_unused_3485_ = lean_ctor_get(v___y_3418_, 0);
                    lean_dec(v_unused_3485_);
                    v___x_3466_ = v___y_3418_;
                    v_isShared_3467_ = v_isSharedCheck_3478_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v___y_3418_);
                    v___x_3466_ = lean_box(0);
                    v_isShared_3467_ = v_isSharedCheck_3478_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3468_ = 3u64;
                v___x_3469_ = lean_uint64_shift_right(v___x_3464_, v___x_3468_);
                v___x_3470_ = lean_uint64_shift_left(v___x_3469_, v___x_3468_);
                v___x_3471_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3430_);
                v_key_3472_ = lean_uint64_lor(v___x_3470_, v___x_3471_);
                v___x_3473_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_3473_, 0, v_config_3463_);
                lean_ctor_set_uint64(
                    v___x_3473_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_3472_,
                );
                if v_isShared_3467_ == 0 {
                    lean_ctor_set(v___x_3466_, 0, v___x_3473_);
                    v___x_3475_ = v___x_3466_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3473_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_zetaDeltaSet_3453_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_lctx_3454_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_localInstances_3455_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_defEqCtx_x3f_3456_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 5, v_synthPendingDepth_3457_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 6, v_canUnfold_x3f_3458_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3477_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_trackZetaDelta_3452_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3477_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v_univApprox_3459_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3477_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_3460_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3477_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_3461_,
                    );
                    v___x_3475_ = v_reuseFailAlloc_3477_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3476_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(v_a_3424_, v_maxArgs_x3f_3416_, v___f_3417_, v___x_3428_, v___x_3428_, v___x_3475_, v___y_3419_, v___y_3420_, v___y_3421_);
                lean_dec(v___y_3421_);
                lean_dec_ref(v___y_3420_);
                lean_dec(v___y_3419_);
                lean_dec_ref(v___x_3475_);
                return v___x_3476_;
            }
            6 => {
                if v_isShared_3492_ == 0 {
                    v___x_3494_ = v___x_3491_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
                    v___x_3494_ = v_reuseFailAlloc_3495_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed(
    mut v_fn_3497_: *mut LeanObject,
    mut v_maxArgs_x3f_3498_: *mut LeanObject,
    mut v___f_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3505_: *mut LeanObject = core::ptr::null_mut();
    v_res_3505_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(
        v_fn_3497_,
        v_maxArgs_x3f_3498_,
        v___f_3499_,
        v___y_3500_,
        v___y_3501_,
        v___y_3502_,
        v___y_3503_,
    );
    return v_res_3505_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(
    mut v_keys_3506_: *mut LeanObject,
    mut v_vals_3507_: *mut LeanObject,
    mut v_i_3508_: *mut LeanObject,
    mut v_k_3509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: u8 = 0;
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3510_ = lean_array_get_size(v_keys_3506_);
                v___x_3511_ = lean_nat_dec_lt(v_i_3508_, v___x_3510_);
                if v___x_3511_ == 0 {
                    lean_dec(v_i_3508_);
                    v___x_3512_ = lean_box(0);
                    return v___x_3512_;
                } else {
                    v_k_x27_3513_ = lean_array_fget_borrowed(v_keys_3506_, v_i_3508_);
                    v___x_3514_ =
                        l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(
                            v_k_3509_,
                            v_k_x27_3513_,
                        );
                    if v___x_3514_ == 0 {
                        v___x_3515_ = lean_unsigned_to_nat(1);
                        v___x_3516_ = lean_nat_add(v_i_3508_, v___x_3515_);
                        lean_dec(v_i_3508_);
                        v_i_3508_ = v___x_3516_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3518_ = lean_array_fget_borrowed(v_vals_3507_, v_i_3508_);
                        lean_dec(v_i_3508_);
                        lean_inc(v___x_3518_);
                        v___x_3519_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3519_, 0, v___x_3518_);
                        return v___x_3519_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg___boxed(
    mut v_keys_3520_: *mut LeanObject,
    mut v_vals_3521_: *mut LeanObject,
    mut v_i_3522_: *mut LeanObject,
    mut v_k_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3524_: *mut LeanObject = core::ptr::null_mut();
    v_res_3524_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_3520_, v_vals_3521_, v_i_3522_, v_k_3523_);
    lean_dec_ref(v_k_3523_);
    lean_dec_ref(v_vals_3521_);
    lean_dec_ref(v_keys_3520_);
    return v_res_3524_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0()
-> usize {
    let mut v___x_3525_: usize = 0;
    let mut v___x_3526_: usize = 0;
    let mut v___x_3527_: usize = 0;
    v___x_3525_ = 5usize;
    v___x_3526_ = 1usize;
    v___x_3527_ = lean_usize_shift_left(v___x_3526_, v___x_3525_);
    return v___x_3527_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1()
-> usize {
    let mut v___x_3528_: usize = 0;
    let mut v___x_3529_: usize = 0;
    let mut v___x_3530_: usize = 0;
    v___x_3528_ = 1usize;
    v___x_3529_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__0);
    v___x_3530_ = lean_usize_sub(v___x_3529_, v___x_3528_);
    return v___x_3530_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(
    mut v_x_3531_: *mut LeanObject,
    mut v_x_3532_: usize,
    mut v_x_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: usize = 0;
    let mut v_j_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: usize = 0;
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3531_) == 0 {
                    v_es_3534_ = lean_ctor_get(v_x_3531_, 0);
                    v___x_3535_ = lean_box(2);
                    v___x_3536_ = 5usize;
                    v___x_3537_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
                    v___x_3538_ = lean_usize_land(v_x_3532_, v___x_3537_);
                    v_j_3539_ = lean_usize_to_nat(v___x_3538_);
                    v___x_3540_ = lean_array_get_borrowed(v___x_3535_, v_es_3534_, v_j_3539_);
                    lean_dec(v_j_3539_);
                    match lean_obj_tag(v___x_3540_) {
                        0 => {
                            v_key_3541_ = lean_ctor_get(v___x_3540_, 0);
                            v_val_3542_ = lean_ctor_get(v___x_3540_, 1);
                            v___x_3543_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(v_x_3533_, v_key_3541_);
                            if v___x_3543_ == 0 {
                                v___x_3544_ = lean_box(0);
                                return v___x_3544_;
                            } else {
                                lean_inc(v_val_3542_);
                                v___x_3545_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3545_, 0, v_val_3542_);
                                return v___x_3545_;
                            }
                        }
                        1 => {
                            v_node_3546_ = lean_ctor_get(v___x_3540_, 0);
                            v___x_3547_ = lean_usize_shift_right(v_x_3532_, v___x_3536_);
                            v_x_3531_ = v_node_3546_;
                            v_x_3532_ = v___x_3547_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3549_ = lean_box(0);
                            return v___x_3549_;
                        }
                    }
                } else {
                    v_ks_3550_ = lean_ctor_get(v_x_3531_, 0);
                    v_vs_3551_ = lean_ctor_get(v_x_3531_, 1);
                    v___x_3552_ = lean_unsigned_to_nat(0);
                    v___x_3553_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_ks_3550_, v_vs_3551_, v___x_3552_, v_x_3533_);
                    return v___x_3553_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___boxed(
    mut v_x_3554_: *mut LeanObject,
    mut v_x_3555_: *mut LeanObject,
    mut v_x_3556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13156__boxed_3557_: usize = 0;
    let mut v_res_3558_: *mut LeanObject = core::ptr::null_mut();
    v_x_13156__boxed_3557_ = lean_unbox_usize(v_x_3555_);
    lean_dec(v_x_3555_);
    v_res_3558_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_3554_, v_x_13156__boxed_3557_, v_x_3556_);
    lean_dec_ref(v_x_3556_);
    lean_dec_ref(v_x_3554_);
    return v_res_3558_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(
    mut v_x_3559_: *mut LeanObject,
    mut v_x_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3561_: u64 = 0;
    let mut v___x_3562_: usize = 0;
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    v___x_3561_ =
        l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_3560_);
    v___x_3562_ = lean_uint64_to_usize(v___x_3561_);
    v___x_3563_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_3559_, v___x_3562_, v_x_3560_);
    return v___x_3563_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg___boxed(
    mut v_x_3564_: *mut LeanObject,
    mut v_x_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3566_: *mut LeanObject = core::ptr::null_mut();
    v_res_3566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_3564_, v_x_3565_);
    lean_dec_ref(v_x_3565_);
    lean_dec_ref(v_x_3564_);
    return v_res_3566_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(
    mut v_x_3567_: *mut LeanObject,
    mut v_x_3568_: *mut LeanObject,
    mut v_x_3569_: *mut LeanObject,
    mut v_x_3570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3571_ = lean_ctor_get(v_x_3567_, 0);
                v_vs_3572_ = lean_ctor_get(v_x_3567_, 1);
                v_isSharedCheck_3596_ = (!lean_is_exclusive(v_x_3567_)) as u8;
                if v_isSharedCheck_3596_ == 0 {
                    v___x_3574_ = v_x_3567_;
                    v_isShared_3575_ = v_isSharedCheck_3596_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3572_);
                    lean_inc(v_ks_3571_);
                    lean_dec(v_x_3567_);
                    v___x_3574_ = lean_box(0);
                    v_isShared_3575_ = v_isSharedCheck_3596_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3576_ = lean_array_get_size(v_ks_3571_);
                v___x_3577_ = lean_nat_dec_lt(v_x_3568_, v___x_3576_);
                if v___x_3577_ == 0 {
                    lean_dec(v_x_3568_);
                    v___x_3578_ = lean_array_push(v_ks_3571_, v_x_3569_);
                    v___x_3579_ = lean_array_push(v_vs_3572_, v_x_3570_);
                    if v_isShared_3575_ == 0 {
                        lean_ctor_set(v___x_3574_, 1, v___x_3579_);
                        lean_ctor_set(v___x_3574_, 0, v___x_3578_);
                        v___x_3581_ = v___x_3574_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3578_);
                        lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3579_);
                        v___x_3581_ = v_reuseFailAlloc_3582_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3583_ = lean_array_fget_borrowed(v_ks_3571_, v_x_3568_);
                    v___x_3584_ =
                        l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(
                            v_x_3569_,
                            v_k_x27_3583_,
                        );
                    if v___x_3584_ == 0 {
                        if v_isShared_3575_ == 0 {
                            v___x_3586_ = v___x_3574_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_ks_3571_);
                            lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_vs_3572_);
                            v___x_3586_ = v_reuseFailAlloc_3590_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3591_ = lean_array_fset(v_ks_3571_, v_x_3568_, v_x_3569_);
                        v___x_3592_ = lean_array_fset(v_vs_3572_, v_x_3568_, v_x_3570_);
                        lean_dec(v_x_3568_);
                        if v_isShared_3575_ == 0 {
                            lean_ctor_set(v___x_3574_, 1, v___x_3592_);
                            lean_ctor_set(v___x_3574_, 0, v___x_3591_);
                            v___x_3594_ = v___x_3574_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3591_);
                            lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3592_);
                            v___x_3594_ = v_reuseFailAlloc_3595_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3581_;
            }
            3 => {
                v___x_3587_ = lean_unsigned_to_nat(1);
                v___x_3588_ = lean_nat_add(v_x_3568_, v___x_3587_);
                lean_dec(v_x_3568_);
                v_x_3567_ = v___x_3586_;
                v_x_3568_ = v___x_3588_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(
    mut v_n_3597_: *mut LeanObject,
    mut v_k_3598_: *mut LeanObject,
    mut v_v_3599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    v___x_3600_ = lean_unsigned_to_nat(0);
    v___x_3601_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_n_3597_, v___x_3600_, v_k_3598_, v_v_3599_);
    return v___x_3601_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    v___x_3602_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3602_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(
    mut v_x_3603_: *mut LeanObject,
    mut v_x_3604_: usize,
    mut v_x_3605_: usize,
    mut v_x_3606_: *mut LeanObject,
    mut v_x_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: usize = 0;
    let mut v___x_3610_: usize = 0;
    let mut v___x_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v_j_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: u8 = 0;
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v_v_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3633_: u8 = 0;
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3639_: u8 = 0;
    let mut v_node_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3644_: usize = 0;
    let mut v___x_3645_: usize = 0;
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut v_unused_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3663_: u8 = 0;
    let mut v_ks_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: usize = 0;
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v_reuseFailAlloc_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3603_) == 0 {
                    v_es_3608_ = lean_ctor_get(v_x_3603_, 0);
                    v___x_3609_ = 5usize;
                    v___x_3610_ = 1usize;
                    v___x_3611_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
                    v___x_3612_ = lean_usize_land(v_x_3604_, v___x_3611_);
                    v_j_3613_ = lean_usize_to_nat(v___x_3612_);
                    v___x_3614_ = lean_array_get_size(v_es_3608_);
                    v___x_3615_ = lean_nat_dec_lt(v_j_3613_, v___x_3614_);
                    if v___x_3615_ == 0 {
                        lean_dec(v_j_3613_);
                        lean_dec(v_x_3607_);
                        lean_dec_ref(v_x_3606_);
                        return v_x_3603_;
                    } else {
                        lean_inc_ref(v_es_3608_);
                        v_isSharedCheck_3652_ = (!lean_is_exclusive(v_x_3603_)) as u8;
                        if v_isSharedCheck_3652_ == 0 {
                            v_unused_3653_ = lean_ctor_get(v_x_3603_, 0);
                            lean_dec(v_unused_3653_);
                            v___x_3617_ = v_x_3603_;
                            v_isShared_3618_ = v_isSharedCheck_3652_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3603_);
                            v___x_3617_ = lean_box(0);
                            v_isShared_3618_ = v_isSharedCheck_3652_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3654_ = lean_ctor_get(v_x_3603_, 0);
                    v_vs_3655_ = lean_ctor_get(v_x_3603_, 1);
                    v_isSharedCheck_3675_ = (!lean_is_exclusive(v_x_3603_)) as u8;
                    if v_isSharedCheck_3675_ == 0 {
                        v___x_3657_ = v_x_3603_;
                        v_isShared_3658_ = v_isSharedCheck_3675_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3655_);
                        lean_inc(v_ks_3654_);
                        lean_dec(v_x_3603_);
                        v___x_3657_ = lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3675_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3619_ = lean_array_fget(v_es_3608_, v_j_3613_);
                v___x_3620_ = lean_box(0);
                v_xs_x27_3621_ = lean_array_fset(v_es_3608_, v_j_3613_, v___x_3620_);
                match lean_obj_tag(v_v_3619_) {
                    0 => {
                        v_key_3628_ = lean_ctor_get(v_v_3619_, 0);
                        v_val_3629_ = lean_ctor_get(v_v_3619_, 1);
                        v_isSharedCheck_3639_ = (!lean_is_exclusive(v_v_3619_)) as u8;
                        if v_isSharedCheck_3639_ == 0 {
                            v___x_3631_ = v_v_3619_;
                            v_isShared_3632_ = v_isSharedCheck_3639_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3629_);
                            lean_inc(v_key_3628_);
                            lean_dec(v_v_3619_);
                            v___x_3631_ = lean_box(0);
                            v_isShared_3632_ = v_isSharedCheck_3639_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3640_ = lean_ctor_get(v_v_3619_, 0);
                        v_isSharedCheck_3650_ = (!lean_is_exclusive(v_v_3619_)) as u8;
                        if v_isSharedCheck_3650_ == 0 {
                            v___x_3642_ = v_v_3619_;
                            v_isShared_3643_ = v_isSharedCheck_3650_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3640_);
                            lean_dec(v_v_3619_);
                            v___x_3642_ = lean_box(0);
                            v_isShared_3643_ = v_isSharedCheck_3650_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3651_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3651_, 0, v_x_3606_);
                        lean_ctor_set(v___x_3651_, 1, v_x_3607_);
                        v___y_3623_ = v___x_3651_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3624_ = lean_array_fset(v_xs_x27_3621_, v_j_3613_, v___y_3623_);
                lean_dec(v_j_3613_);
                if v_isShared_3618_ == 0 {
                    lean_ctor_set(v___x_3617_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3617_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3626_;
            }
            4 => {
                v___x_3633_ =
                    l___private_Lean_Meta_FunInfo_0__Lean_Meta_instBEqFunInfoEnvCacheKey_beq(
                        v_x_3606_,
                        v_key_3628_,
                    );
                if v___x_3633_ == 0 {
                    lean_del_object(v___x_3631_);
                    v___x_3634_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3628_,
                        v_val_3629_,
                        v_x_3606_,
                        v_x_3607_,
                    );
                    v___x_3635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3635_, 0, v___x_3634_);
                    v___y_3623_ = v___x_3635_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3629_);
                    lean_dec(v_key_3628_);
                    if v_isShared_3632_ == 0 {
                        lean_ctor_set(v___x_3631_, 1, v_x_3607_);
                        lean_ctor_set(v___x_3631_, 0, v_x_3606_);
                        v___x_3637_ = v___x_3631_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_x_3606_);
                        lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_x_3607_);
                        v___x_3637_ = v_reuseFailAlloc_3638_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3623_ = v___x_3637_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3644_ = lean_usize_shift_right(v_x_3604_, v___x_3609_);
                v___x_3645_ = lean_usize_add(v_x_3605_, v___x_3610_);
                v___x_3646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_node_3640_, v___x_3644_, v___x_3645_, v_x_3606_, v_x_3607_);
                if v_isShared_3643_ == 0 {
                    lean_ctor_set(v___x_3642_, 0, v___x_3646_);
                    v___x_3648_ = v___x_3642_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
                    v___x_3648_ = v_reuseFailAlloc_3649_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3623_ = v___x_3648_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3658_ == 0 {
                    v___x_3660_ = v___x_3657_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_ks_3654_);
                    lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_vs_3655_);
                    v___x_3660_ = v_reuseFailAlloc_3674_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3661_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v___x_3660_, v_x_3606_, v_x_3607_);
                v___x_3669_ = 7usize;
                v___x_3670_ = lean_usize_dec_le(v___x_3669_, v_x_3605_);
                if v___x_3670_ == 0 {
                    v___x_3671_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3661_);
                    v___x_3672_ = lean_unsigned_to_nat(4);
                    v___x_3673_ = lean_nat_dec_lt(v___x_3671_, v___x_3672_);
                    lean_dec(v___x_3671_);
                    v___y_3663_ = v___x_3673_;
                    state = 10;
                    continue;
                } else {
                    v___y_3663_ = v___x_3670_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3663_ == 0 {
                    v_ks_3664_ = lean_ctor_get(v_newNode_3661_, 0);
                    lean_inc_ref(v_ks_3664_);
                    v_vs_3665_ = lean_ctor_get(v_newNode_3661_, 1);
                    lean_inc_ref(v_vs_3665_);
                    lean_dec_ref(v_newNode_3661_);
                    v___x_3666_ = lean_unsigned_to_nat(0);
                    v___x_3667_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___closed__0);
                    v___x_3668_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_x_3605_, v_ks_3664_, v_vs_3665_, v___x_3666_, v___x_3667_);
                    lean_dec_ref(v_vs_3665_);
                    lean_dec_ref(v_ks_3664_);
                    return v___x_3668_;
                } else {
                    return v_newNode_3661_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(
    mut v_depth_3676_: usize,
    mut v_keys_3677_: *mut LeanObject,
    mut v_vals_3678_: *mut LeanObject,
    mut v_i_3679_: *mut LeanObject,
    mut v_entries_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v_k_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: u64 = 0;
    let mut v_h_3686_: usize = 0;
    let mut v___x_3687_: usize = 0;
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: usize = 0;
    let mut v___x_3690_: usize = 0;
    let mut v___x_3691_: usize = 0;
    let mut v_h_3692_: usize = 0;
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3681_ = lean_array_get_size(v_keys_3677_);
                v___x_3682_ = lean_nat_dec_lt(v_i_3679_, v___x_3681_);
                if v___x_3682_ == 0 {
                    lean_dec(v_i_3679_);
                    return v_entries_3680_;
                } else {
                    v_k_3683_ = lean_array_fget_borrowed(v_keys_3677_, v_i_3679_);
                    v_v_3684_ = lean_array_fget_borrowed(v_vals_3678_, v_i_3679_);
                    v___x_3685_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_k_3683_);
                    v_h_3686_ = lean_uint64_to_usize(v___x_3685_);
                    v___x_3687_ = 5usize;
                    v___x_3688_ = lean_unsigned_to_nat(1);
                    v___x_3689_ = 1usize;
                    v___x_3690_ = lean_usize_sub(v_depth_3676_, v___x_3689_);
                    v___x_3691_ = lean_usize_mul(v___x_3687_, v___x_3690_);
                    v_h_3692_ = lean_usize_shift_right(v_h_3686_, v___x_3691_);
                    v___x_3693_ = lean_nat_add(v_i_3679_, v___x_3688_);
                    lean_dec(v_i_3679_);
                    lean_inc(v_v_3684_);
                    lean_inc(v_k_3683_);
                    v___x_3694_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_entries_3680_, v_h_3692_, v_depth_3676_, v_k_3683_, v_v_3684_);
                    v_i_3679_ = v___x_3693_;
                    v_entries_3680_ = v___x_3694_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg___boxed(
    mut v_depth_3696_: *mut LeanObject,
    mut v_keys_3697_: *mut LeanObject,
    mut v_vals_3698_: *mut LeanObject,
    mut v_i_3699_: *mut LeanObject,
    mut v_entries_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3701_: usize = 0;
    let mut v_res_3702_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3701_ = lean_unbox_usize(v_depth_3696_);
    lean_dec(v_depth_3696_);
    v_res_3702_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_boxed_3701_, v_keys_3697_, v_vals_3698_, v_i_3699_, v_entries_3700_);
    lean_dec_ref(v_vals_3698_);
    lean_dec_ref(v_keys_3697_);
    return v_res_3702_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg___boxed(
    mut v_x_3703_: *mut LeanObject,
    mut v_x_3704_: *mut LeanObject,
    mut v_x_3705_: *mut LeanObject,
    mut v_x_3706_: *mut LeanObject,
    mut v_x_3707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13303__boxed_3708_: usize = 0;
    let mut v_x_13304__boxed_3709_: usize = 0;
    let mut v_res_3710_: *mut LeanObject = core::ptr::null_mut();
    v_x_13303__boxed_3708_ = lean_unbox_usize(v_x_3704_);
    lean_dec(v_x_3704_);
    v_x_13304__boxed_3709_ = lean_unbox_usize(v_x_3705_);
    lean_dec(v_x_3705_);
    v_res_3710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_3703_, v_x_13303__boxed_3708_, v_x_13304__boxed_3709_, v_x_3706_, v_x_3707_);
    return v_res_3710_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(
    mut v_x_3711_: *mut LeanObject,
    mut v_x_3712_: *mut LeanObject,
    mut v_x_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3714_: u64 = 0;
    let mut v___x_3715_: usize = 0;
    let mut v___x_3716_: usize = 0;
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    v___x_3714_ =
        l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash(v_x_3712_);
    v___x_3715_ = lean_uint64_to_usize(v___x_3714_);
    v___x_3716_ = 1usize;
    v___x_3717_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_3711_, v___x_3715_, v___x_3716_, v_x_3712_, v_x_3713_);
    return v___x_3717_;
}
pub unsafe fn _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    v___x_3718_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3718_;
}
pub unsafe fn _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3719_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0_once), _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__0);
    v___x_3720_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3720_, 0, v___x_3719_);
    return v___x_3720_;
}
pub unsafe fn l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(
    mut v_realizeMapRef_3721_: *mut LeanObject,
    mut v_env_3722_: *mut LeanObject,
    mut v_forConst_3723_: *mut LeanObject,
    mut v_ctx_3724_: *mut LeanObject,
    mut v_importRealizationCtx_x3f_3725_: *mut LeanObject,
    mut v_realize_3726_: *mut LeanObject,
    mut v_opts_3727_: *mut LeanObject,
    mut v_key_3728_: *mut LeanObject,
    mut v_inst_3729_: *mut LeanObject,
    mut v_____r_3730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3746_: u8 = 0;
    let mut v_base_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_serverBaseExts_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncConstsMap_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncCtx_x3f_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localRealizationCtxMap_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allRealizations_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3754_: u8 = 0;
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_unused_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3732_ = lean_io_promise_new();
                v___x_3733_ = lean_st_ref_take(v_realizeMapRef_3721_);
                v___x_3773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3733_, v_inst_3729_);
                if lean_obj_tag(v___x_3773_) == 0 {
                    v___x_3774_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1_once), _init_l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___closed__1);
                    v___y_3768_ = v___x_3774_;
                    state = 6;
                    continue;
                } else {
                    v_val_3775_ = lean_ctor_get(v___x_3773_, 0);
                    lean_inc(v_val_3775_);
                    lean_dec_ref_known(v___x_3773_, 1);
                    v___y_3768_ = v_val_3775_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_3737_ = lean_st_ref_set(v_realizeMapRef_3721_, v_snd_3736_);
                if lean_obj_tag(v_fst_3735_) == 1 {
                    lean_dec(v___x_3732_);
                    lean_dec_ref(v_opts_3727_);
                    lean_dec_ref(v_realize_3726_);
                    lean_dec(v_importRealizationCtx_x3f_3725_);
                    lean_dec_ref(v_ctx_3724_);
                    lean_dec(v_forConst_3723_);
                    lean_dec(v_env_3722_);
                    v_val_3738_ = lean_ctor_get(v_fst_3735_, 0);
                    v_isSharedCheck_3746_ = (!lean_is_exclusive(v_fst_3735_)) as u8;
                    if v_isSharedCheck_3746_ == 0 {
                        v___x_3740_ = v_fst_3735_;
                        v_isShared_3741_ = v_isSharedCheck_3746_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3738_);
                        lean_dec(v_fst_3735_);
                        v___x_3740_ = lean_box(0);
                        v_isShared_3741_ = v_isSharedCheck_3746_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_3735_);
                    v_base_3747_ = lean_ctor_get(v_env_3722_, 0);
                    v_serverBaseExts_3748_ = lean_ctor_get(v_env_3722_, 1);
                    v_checked_3749_ = lean_ctor_get(v_env_3722_, 2);
                    v_asyncConstsMap_3750_ = lean_ctor_get(v_env_3722_, 3);
                    v_asyncCtx_x3f_3751_ = lean_ctor_get(v_env_3722_, 4);
                    v_localRealizationCtxMap_3752_ = lean_ctor_get(v_env_3722_, 6);
                    v_allRealizations_3753_ = lean_ctor_get(v_env_3722_, 7);
                    v_isExporting_3754_ = lean_ctor_get_uint8(
                        v_env_3722_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    v_isSharedCheck_3765_ = (!lean_is_exclusive(v_env_3722_)) as u8;
                    if v_isSharedCheck_3765_ == 0 {
                        v_unused_3766_ = lean_ctor_get(v_env_3722_, 5);
                        lean_dec(v_unused_3766_);
                        v___x_3756_ = v_env_3722_;
                        v_isShared_3757_ = v_isSharedCheck_3765_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_allRealizations_3753_);
                        lean_inc(v_localRealizationCtxMap_3752_);
                        lean_inc(v_asyncCtx_x3f_3751_);
                        lean_inc(v_asyncConstsMap_3750_);
                        lean_inc(v_checked_3749_);
                        lean_inc(v_serverBaseExts_3748_);
                        lean_inc(v_base_3747_);
                        lean_dec(v_env_3722_);
                        v___x_3756_ = lean_box(0);
                        v_isShared_3757_ = v_isSharedCheck_3765_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3742_ = lean_task_get_own(v_val_3738_);
                if v_isShared_3741_ == 0 {
                    lean_ctor_set_tag(v___x_3740_, 0);
                    lean_ctor_set(v___x_3740_, 0, v___x_3742_);
                    v___x_3744_ = v___x_3740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
                    v___x_3744_ = v_reuseFailAlloc_3745_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3744_;
            }
            4 => {
                v___x_3758_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_forConst_3723_, v_ctx_3724_, v_localRealizationCtxMap_3752_);
                if v_isShared_3757_ == 0 {
                    lean_ctor_set(v___x_3756_, 6, v___x_3758_);
                    lean_ctor_set(v___x_3756_, 5, v_importRealizationCtx_x3f_3725_);
                    v___x_3760_ = v___x_3756_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 8, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_base_3747_);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_serverBaseExts_3748_);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_checked_3749_);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_asyncConstsMap_3750_);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 4, v_asyncCtx_x3f_3751_);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 5, v_importRealizationCtx_x3f_3725_);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 6, v___x_3758_);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 7, v_allRealizations_3753_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3764_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        v_isExporting_3754_,
                    );
                    v___x_3760_ = v_reuseFailAlloc_3764_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3761_ = lean_apply_3(v_realize_3726_, v___x_3760_, v_opts_3727_, lean_box(0));
                lean_inc(v___x_3761_);
                v___x_3762_ = lean_io_promise_resolve(v___x_3761_, v___x_3732_);
                lean_dec(v___x_3732_);
                v___x_3763_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3763_, 0, v___x_3761_);
                return v___x_3763_;
            }
            6 => {
                v___x_3769_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v___y_3768_, v_key_3728_);
                if lean_obj_tag(v___x_3769_) == 0 {
                    v___x_3770_ = l_IO_Promise_result_x21___redArg(v___x_3732_);
                    v___x_3771_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v___y_3768_, v_key_3728_, v___x_3770_);
                    v___x_3772_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_inst_3729_, v___x_3771_, v___x_3733_);
                    v_fst_3735_ = v___x_3769_;
                    v_snd_3736_ = v___x_3772_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_3768_);
                    lean_dec(v_inst_3729_);
                    lean_dec_ref(v_key_3728_);
                    v_fst_3735_ = v___x_3769_;
                    v_snd_3736_ = v___x_3733_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0___boxed(
    mut v_realizeMapRef_3776_: *mut LeanObject,
    mut v_env_3777_: *mut LeanObject,
    mut v_forConst_3778_: *mut LeanObject,
    mut v_ctx_3779_: *mut LeanObject,
    mut v_importRealizationCtx_x3f_3780_: *mut LeanObject,
    mut v_realize_3781_: *mut LeanObject,
    mut v_opts_3782_: *mut LeanObject,
    mut v_key_3783_: *mut LeanObject,
    mut v_inst_3784_: *mut LeanObject,
    mut v_____r_3785_: *mut LeanObject,
    mut v___y_3786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3787_: *mut LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_3776_, v_env_3777_, v_forConst_3778_, v_ctx_3779_, v_importRealizationCtx_x3f_3780_, v_realize_3781_, v_opts_3782_, v_key_3783_, v_inst_3784_, v_____r_3785_);
    lean_dec(v_realizeMapRef_3776_);
    return v_res_3787_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(
    mut v_a_3788_: *mut LeanObject,
    mut v_x_3789_: *mut LeanObject,
) -> u8 {
    let mut v___x_3790_: u8 = 0;
    let mut v_key_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3789_) == 0 {
                    v___x_3790_ = 0;
                    return v___x_3790_;
                } else {
                    v_key_3791_ = lean_ctor_get(v_x_3789_, 0);
                    v_tail_3792_ = lean_ctor_get(v_x_3789_, 2);
                    v___x_3793_ = lean_name_eq(v_key_3791_, v_a_3788_);
                    if v___x_3793_ == 0 {
                        v_x_3789_ = v_tail_3792_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3793_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg___boxed(
    mut v_a_3795_: *mut LeanObject,
    mut v_x_3796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3797_: u8 = 0;
    let mut v_r_3798_: *mut LeanObject = core::ptr::null_mut();
    v_res_3797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_3795_, v_x_3796_);
    lean_dec(v_x_3796_);
    lean_dec(v_a_3795_);
    v_r_3798_ = lean_box((v_res_3797_) as usize);
    return v_r_3798_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(
    mut v_m_3799_: *mut LeanObject,
    mut v_a_3800_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: u64 = 0;
    let mut v___x_3805_: u64 = 0;
    let mut v___x_3806_: u64 = 0;
    let mut v_fold_3807_: u64 = 0;
    let mut v___x_3808_: u64 = 0;
    let mut v___x_3809_: u64 = 0;
    let mut v___x_3810_: u64 = 0;
    let mut v___x_3811_: usize = 0;
    let mut v___x_3812_: usize = 0;
    let mut v___x_3813_: usize = 0;
    let mut v___x_3814_: usize = 0;
    let mut v___x_3815_: usize = 0;
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: u8 = 0;
    let mut v___x_3818_: u64 = 0;
    let mut v_hash_3819_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3801_ = lean_ctor_get(v_m_3799_, 1);
                v___x_3802_ = lean_array_get_size(v_buckets_3801_);
                if lean_obj_tag(v_a_3800_) == 0 {
                    v___x_3818_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0_once), _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_instHashableFunInfoEnvCacheKey_hash___closed__0);
                    v___y_3804_ = v___x_3818_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3819_ = lean_ctor_get_uint64(
                        v_a_3800_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3804_ = v_hash_3819_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3805_ = 32u64;
                v___x_3806_ = lean_uint64_shift_right(v___y_3804_, v___x_3805_);
                v_fold_3807_ = lean_uint64_xor(v___y_3804_, v___x_3806_);
                v___x_3808_ = 16u64;
                v___x_3809_ = lean_uint64_shift_right(v_fold_3807_, v___x_3808_);
                v___x_3810_ = lean_uint64_xor(v_fold_3807_, v___x_3809_);
                v___x_3811_ = lean_uint64_to_usize(v___x_3810_);
                v___x_3812_ = lean_usize_of_nat(v___x_3802_);
                v___x_3813_ = 1usize;
                v___x_3814_ = lean_usize_sub(v___x_3812_, v___x_3813_);
                v___x_3815_ = lean_usize_land(v___x_3811_, v___x_3814_);
                v___x_3816_ = lean_array_uget_borrowed(v_buckets_3801_, v___x_3815_);
                v___x_3817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_3800_, v___x_3816_);
                return v___x_3817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg___boxed(
    mut v_m_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3822_: u8 = 0;
    let mut v_r_3823_: *mut LeanObject = core::ptr::null_mut();
    v_res_3822_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_3820_, v_a_3821_);
    lean_dec(v_a_3821_);
    lean_dec_ref(v_m_3820_);
    v_r_3823_ = lean_box((v_res_3822_) as usize);
    return v_r_3823_;
}
pub unsafe fn l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(
    mut v_inst_3830_: *mut LeanObject,
    mut v_env_3831_: *mut LeanObject,
    mut v_forConst_3832_: *mut LeanObject,
    mut v_key_3833_: *mut LeanObject,
    mut v_realize_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_base_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importRealizationCtx_x3f_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localRealizationCtxMap_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3847_: u8 = 0;
    let mut v_ctx_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_realizeMapRef_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_const2ModIdx_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: u8 = 0;
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_private_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_public_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3836_ = lean_io_get_num_heartbeats();
                v_base_3844_ = lean_ctor_get(v_env_3831_, 0);
                lean_inc_ref(v_base_3844_);
                v_importRealizationCtx_x3f_3845_ = lean_ctor_get(v_env_3831_, 5);
                lean_inc(v_importRealizationCtx_x3f_3845_);
                v_localRealizationCtxMap_3846_ = lean_ctor_get(v_env_3831_, 6);
                lean_inc(v_localRealizationCtxMap_3846_);
                v_isExporting_3847_ = lean_ctor_get_uint8(
                    v_env_3831_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_3831_);
                if v_isExporting_3847_ == 0 {
                    v_private_3884_ = lean_ctor_get(v_base_3844_, 0);
                    lean_inc(v_private_3884_);
                    lean_dec_ref(v_base_3844_);
                    v___y_3864_ = v_private_3884_;
                    state = 4;
                    continue;
                } else {
                    v_public_3885_ = lean_ctor_get(v_base_3844_, 1);
                    lean_inc(v_public_3885_);
                    lean_dec_ref(v_base_3844_);
                    v___y_3864_ = v_public_3885_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_3839_ = lean_io_set_heartbeats(v___x_3836_);
                v___x_3840_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3840_, 0, v_a_3838_);
                return v___x_3840_;
            }
            2 => {
                v_a_3843_ = lean_ctor_get(v___y_3842_, 0);
                lean_inc(v_a_3843_);
                lean_dec_ref(v___y_3842_);
                v_a_3838_ = v_a_3843_;
                state = 1;
                continue;
            }
            3 => {
                v_env_3850_ = lean_ctor_get(v_ctx_3849_, 0);
                lean_inc(v_env_3850_);
                v_opts_3851_ = lean_ctor_get(v_ctx_3849_, 1);
                lean_inc_ref(v_opts_3851_);
                v_realizeMapRef_3852_ = lean_ctor_get(v_ctx_3849_, 2);
                lean_inc(v_realizeMapRef_3852_);
                v___x_3853_ = lean_st_ref_get(v_realizeMapRef_3852_);
                v___x_3854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3853_, v_inst_3830_);
                lean_dec(v___x_3853_);
                if lean_obj_tag(v___x_3854_) == 1 {
                    v_val_3855_ = lean_ctor_get(v___x_3854_, 0);
                    lean_inc(v_val_3855_);
                    lean_dec_ref_known(v___x_3854_, 1);
                    v___x_3856_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_val_3855_, v_key_3833_);
                    lean_dec(v_val_3855_);
                    if lean_obj_tag(v___x_3856_) == 1 {
                        lean_dec(v_realizeMapRef_3852_);
                        lean_dec_ref(v_opts_3851_);
                        lean_dec(v_env_3850_);
                        lean_dec_ref(v_ctx_3849_);
                        lean_dec(v_importRealizationCtx_x3f_3845_);
                        lean_dec_ref(v_realize_3834_);
                        lean_dec_ref(v_key_3833_);
                        lean_dec(v_forConst_3832_);
                        lean_dec(v_inst_3830_);
                        v_val_3857_ = lean_ctor_get(v___x_3856_, 0);
                        lean_inc(v_val_3857_);
                        lean_dec_ref_known(v___x_3856_, 1);
                        v___x_3858_ = lean_task_get_own(v_val_3857_);
                        v_a_3838_ = v___x_3858_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3856_);
                        v___x_3859_ = lean_box(0);
                        v___x_3860_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_3852_, v_env_3850_, v_forConst_3832_, v_ctx_3849_, v_importRealizationCtx_x3f_3845_, v_realize_3834_, v_opts_3851_, v_key_3833_, v_inst_3830_, v___x_3859_);
                        lean_dec(v_realizeMapRef_3852_);
                        v___y_3842_ = v___x_3860_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3854_);
                    v___x_3861_ = lean_box(0);
                    v___x_3862_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___lam__0(v_realizeMapRef_3852_, v_env_3850_, v_forConst_3832_, v_ctx_3849_, v_importRealizationCtx_x3f_3845_, v_realize_3834_, v_opts_3851_, v_key_3833_, v_inst_3830_, v___x_3861_);
                    lean_dec(v_realizeMapRef_3852_);
                    v___y_3842_ = v___x_3862_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_const2ModIdx_3865_ = lean_ctor_get(v___y_3864_, 2);
                lean_inc_ref(v_const2ModIdx_3865_);
                lean_dec_ref(v___y_3864_);
                v___x_3866_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_const2ModIdx_3865_, v_forConst_3832_);
                lean_dec_ref(v_const2ModIdx_3865_);
                if v___x_3866_ == 0 {
                    v___x_3867_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localRealizationCtxMap_3846_, v_forConst_3832_);
                    lean_dec(v_localRealizationCtxMap_3846_);
                    if lean_obj_tag(v___x_3867_) == 0 {
                        lean_dec(v_importRealizationCtx_x3f_3845_);
                        lean_dec(v___x_3836_);
                        lean_dec_ref(v_realize_3834_);
                        lean_dec_ref(v_key_3833_);
                        v___x_3868_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__0;
                        v___x_3869_ = 1;
                        v___x_3870_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_inst_3830_,
                                v___x_3869_,
                            );
                        v___x_3871_ = lean_string_append(v___x_3868_, v___x_3870_);
                        lean_dec_ref(v___x_3870_);
                        v___x_3872_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__1;
                        v___x_3873_ = lean_string_append(v___x_3871_, v___x_3872_);
                        v___x_3874_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_forConst_3832_,
                                v___x_3869_,
                            );
                        v___x_3875_ = lean_string_append(v___x_3873_, v___x_3874_);
                        lean_dec_ref(v___x_3874_);
                        v___x_3876_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__2;
                        v___x_3877_ = lean_string_append(v___x_3875_, v___x_3876_);
                        v___x_3878_ = lean_alloc_ctor(18, 1, (0) as u32);
                        lean_ctor_set(v___x_3878_, 0, v___x_3877_);
                        v___x_3879_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3879_, 0, v___x_3878_);
                        return v___x_3879_;
                    } else {
                        v_val_3880_ = lean_ctor_get(v___x_3867_, 0);
                        lean_inc(v_val_3880_);
                        lean_dec_ref_known(v___x_3867_, 1);
                        v_ctx_3849_ = v_val_3880_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_localRealizationCtxMap_3846_);
                    if lean_obj_tag(v_importRealizationCtx_x3f_3845_) == 0 {
                        lean_dec(v___x_3836_);
                        lean_dec_ref(v_realize_3834_);
                        lean_dec_ref(v_key_3833_);
                        lean_dec(v_forConst_3832_);
                        lean_dec(v_inst_3830_);
                        v___x_3881_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___closed__4;
                        v___x_3882_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3882_, 0, v___x_3881_);
                        return v___x_3882_;
                    } else {
                        v_val_3883_ = lean_ctor_get(v_importRealizationCtx_x3f_3845_, 0);
                        lean_inc(v_val_3883_);
                        v_ctx_3849_ = v_val_3883_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11___boxed(
    mut v_inst_3886_: *mut LeanObject,
    mut v_env_3887_: *mut LeanObject,
    mut v_forConst_3888_: *mut LeanObject,
    mut v_key_3889_: *mut LeanObject,
    mut v_realize_3890_: *mut LeanObject,
    mut v_a_3891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3892_: *mut LeanObject = core::ptr::null_mut();
    v_res_3892_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_3886_, v_env_3887_, v_forConst_3888_, v_key_3889_, v_realize_3890_);
    return v_res_3892_;
}
pub unsafe fn l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(
    mut v_msg_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
    mut v___y_3896_: *mut LeanObject,
    mut v___y_3897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11419__overap_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    v___f_3899_ =
        l_panic___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___closed__0;
    v___x_11419__overap_3900_ = lean_panic_fn_borrowed(v___f_3899_, v_msg_3893_);
    lean_inc(v___y_3897_);
    lean_inc_ref(v___y_3896_);
    lean_inc(v___y_3895_);
    lean_inc_ref(v___y_3894_);
    v___x_3901_ = lean_apply_5(
        v___x_11419__overap_3900_,
        v___y_3894_,
        v___y_3895_,
        v___y_3896_,
        v___y_3897_,
        lean_box(0),
    );
    return v___x_3901_;
}
pub unsafe fn l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg___boxed(
    mut v_msg_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
    mut v___y_3907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3908_: *mut LeanObject = core::ptr::null_mut();
    v_res_3908_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
    lean_dec(v___y_3906_);
    lean_dec_ref(v___y_3905_);
    lean_dec(v___y_3904_);
    lean_dec_ref(v___y_3903_);
    return v_res_3908_;
}
pub unsafe fn l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(
    mut v_realize_3909_: *mut LeanObject,
    mut v_inst_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v_a_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3929_: u8 = 0;
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3914_);
                lean_inc_ref(v___y_3913_);
                lean_inc(v___y_3912_);
                v___x_3916_ = lean_apply_5(
                    v_realize_3909_,
                    v___y_3911_,
                    v___y_3912_,
                    v___y_3913_,
                    v___y_3914_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3916_) == 0 {
                    v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
                    v_isSharedCheck_3925_ = (!lean_is_exclusive(v___x_3916_)) as u8;
                    if v_isSharedCheck_3925_ == 0 {
                        v___x_3919_ = v___x_3916_;
                        v_isShared_3920_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3917_);
                        lean_dec(v___x_3916_);
                        v___x_3919_ = lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_inst_3910_);
                    v_a_3926_ = lean_ctor_get(v___x_3916_, 0);
                    v_isSharedCheck_3933_ = (!lean_is_exclusive(v___x_3916_)) as u8;
                    if v_isSharedCheck_3933_ == 0 {
                        v___x_3928_ = v___x_3916_;
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3926_);
                        lean_dec(v___x_3916_);
                        v___x_3928_ = lean_box(0);
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3921_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3921_, 0, v_inst_3910_);
                lean_ctor_set(v___x_3921_, 1, v_a_3917_);
                if v_isShared_3920_ == 0 {
                    lean_ctor_set(v___x_3919_, 0, v___x_3921_);
                    v___x_3923_ = v___x_3919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
                    v___x_3923_ = v_reuseFailAlloc_3924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3923_;
            }
            3 => {
                if v_isShared_3929_ == 0 {
                    v___x_3931_ = v___x_3928_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
                    v___x_3931_ = v_reuseFailAlloc_3932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed(
    mut v_realize_3934_: *mut LeanObject,
    mut v_inst_3935_: *mut LeanObject,
    mut v___y_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
    mut v___y_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3941_: *mut LeanObject = core::ptr::null_mut();
    v_res_3941_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0(v_realize_3934_, v_inst_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
    lean_dec(v___y_3939_);
    lean_dec_ref(v___y_3938_);
    lean_dec(v___y_3937_);
    return v_res_3941_;
}
pub unsafe fn _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_Lean_Options_empty;
    v___x_3943_ = l_Lean_Core_getMaxHeartbeats(v___x_3942_);
    return v___x_3943_;
}
pub unsafe fn _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    v___x_3944_ = lean_box(0);
    v___x_3945_ = lean_unsigned_to_nat(16);
    v___x_3946_ = lean_mk_array(v___x_3945_, v___x_3944_);
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    v___x_3947_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1_once), _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__1);
    v___x_3948_ = lean_unsigned_to_nat(0);
    v___x_3949_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3949_, 0, v___x_3948_);
    lean_ctor_set(v___x_3949_, 1, v___x_3947_);
    return v___x_3949_;
}
pub unsafe fn _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    v___x_3952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4;
    v___x_3953_ = lean_unsigned_to_nat(36);
    v___x_3954_ = lean_unsigned_to_nat(2619);
    v___x_3955_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4;
    v___x_3956_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3;
    v___x_3957_ = l_mkPanicMessageWithDecl(
        v___x_3956_,
        v___x_3955_,
        v___x_3954_,
        v___x_3953_,
        v___x_3952_,
    );
    return v___x_3957_;
}
pub unsafe fn _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    v___x_3958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg___closed__4;
    v___x_3959_ = lean_unsigned_to_nat(48);
    v___x_3960_ = lean_unsigned_to_nat(2610);
    v___x_3961_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__4;
    v___x_3962_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__3;
    v___x_3963_ = l_mkPanicMessageWithDecl(
        v___x_3962_,
        v___x_3961_,
        v___x_3960_,
        v___x_3959_,
        v___x_3958_,
    );
    return v___x_3963_;
}
pub unsafe fn l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(
    mut v_inst_3964_: *mut LeanObject,
    mut v_inst_3965_: *mut LeanObject,
    mut v_forConst_3966_: *mut LeanObject,
    mut v_key_3967_: *mut LeanObject,
    mut v_realize_3968_: *mut LeanObject,
    mut v_a_3969_: *mut LeanObject,
    mut v_a_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: u8 = 0;
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: u8 = 0;
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_x3f_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4034_: u8 = 0;
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_val_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4049_: u8 = 0;
    let mut v_a_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3974_ = lean_st_ref_get(v_a_3972_);
                v_env_3975_ = lean_ctor_get(v___x_3974_, 0);
                lean_inc_ref(v_env_3975_);
                lean_dec(v___x_3974_);
                v___x_3976_ = l_Lean_Environment_areRealizationsEnabledForConst(
                    v_env_3975_,
                    v_forConst_3966_,
                );
                if v___x_3976_ == 0 {
                    lean_dec_ref(v_env_3975_);
                    lean_dec_ref(v_key_3967_);
                    lean_dec(v_forConst_3966_);
                    lean_dec(v_inst_3965_);
                    lean_dec(v_inst_3964_);
                    lean_inc(v_a_3972_);
                    lean_inc_ref(v_a_3971_);
                    lean_inc(v_a_3970_);
                    lean_inc_ref(v_a_3969_);
                    v___x_3977_ = lean_apply_5(
                        v_realize_3968_,
                        v_a_3969_,
                        v_a_3970_,
                        v_a_3971_,
                        v_a_3972_,
                        lean_box(0),
                    );
                    return v___x_3977_;
                } else {
                    v___x_3978_ = lean_io_get_num_heartbeats();
                    v_fileName_3979_ = lean_ctor_get(v_a_3971_, 0);
                    v_fileMap_3980_ = lean_ctor_get(v_a_3971_, 1);
                    v_ref_3981_ = lean_ctor_get(v_a_3971_, 5);
                    lean_inc(v_inst_3965_);
                    v___f_3982_ = lean_alloc_closure(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                    lean_closure_set(v___f_3982_, 0, v_realize_3968_);
                    lean_closure_set(v___f_3982_, 1, v_inst_3965_);
                    v___x_3983_ = 0;
                    v___x_3984_ = l_Lean_Options_empty;
                    v___x_3985_ = lean_unsigned_to_nat(0);
                    v___x_3986_ = lean_unsigned_to_nat(1000);
                    v___x_3987_ = lean_box(0);
                    v___x_3988_ = lean_box(0);
                    v___x_3989_ = lean_box(0);
                    v___x_3990_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0_once), _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__0);
                    v___x_3991_ = l_Lean_firstFrontendMacroScope;
                    v___x_3992_ = lean_box(0);
                    v___x_3993_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2_once), _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__2);
                    lean_inc_ref(v_fileMap_3980_);
                    lean_inc_ref(v_fileName_3979_);
                    v___x_3994_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v___x_3994_, 0, v_fileName_3979_);
                    lean_ctor_set(v___x_3994_, 1, v_fileMap_3980_);
                    lean_ctor_set(v___x_3994_, 2, v___x_3984_);
                    lean_ctor_set(v___x_3994_, 3, v___x_3985_);
                    lean_ctor_set(v___x_3994_, 4, v___x_3986_);
                    lean_ctor_set(v___x_3994_, 5, v___x_3987_);
                    lean_ctor_set(v___x_3994_, 6, v___x_3988_);
                    lean_ctor_set(v___x_3994_, 7, v___x_3989_);
                    lean_ctor_set(v___x_3994_, 8, v___x_3978_);
                    lean_ctor_set(v___x_3994_, 9, v___x_3990_);
                    lean_ctor_set(v___x_3994_, 10, v___x_3988_);
                    lean_ctor_set(v___x_3994_, 11, v___x_3991_);
                    lean_ctor_set(v___x_3994_, 12, v___x_3992_);
                    lean_ctor_set(v___x_3994_, 13, v___x_3993_);
                    lean_ctor_set_uint8(
                        v___x_3994_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v___x_3983_,
                    );
                    lean_ctor_set_uint8(
                        v___x_3994_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v___x_3983_,
                    );
                    v___x_3995_ = lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_realizeValue_realizeAndReport___boxed as *mut core::ffi::c_void, 5, 2);
                    lean_closure_set(v___x_3995_, 0, v___f_3982_);
                    lean_closure_set(v___x_3995_, 1, v___x_3994_);
                    v___x_3996_ = l_Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11(v_inst_3964_, v_env_3975_, v_forConst_3966_, v_key_3967_, v___x_3995_);
                    if lean_obj_tag(v___x_3996_) == 0 {
                        v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
                        v_isSharedCheck_4049_ = (!lean_is_exclusive(v___x_3996_)) as u8;
                        if v_isSharedCheck_4049_ == 0 {
                            v___x_3999_ = v___x_3996_;
                            v_isShared_4000_ = v_isSharedCheck_4049_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3997_);
                            lean_dec(v___x_3996_);
                            v___x_3999_ = lean_box(0);
                            v_isShared_4000_ = v_isSharedCheck_4049_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_inst_3965_);
                        v_a_4050_ = lean_ctor_get(v___x_3996_, 0);
                        v_isSharedCheck_4061_ = (!lean_is_exclusive(v___x_3996_)) as u8;
                        if v_isSharedCheck_4061_ == 0 {
                            v___x_4052_ = v___x_3996_;
                            v_isShared_4053_ = v_isSharedCheck_4061_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4050_);
                            lean_dec(v___x_3996_);
                            v___x_4052_ = lean_box(0);
                            v_isShared_4053_ = v_isSharedCheck_4061_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4001_ = l___private_Lean_Meta_Basic_0__Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_373817412____hygCtx___hyg_13_;
                v___x_4002_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                    v_a_3997_,
                    v___x_4001_,
                );
                lean_dec(v_a_3997_);
                if lean_obj_tag(v___x_4002_) == 1 {
                    v_val_4003_ = lean_ctor_get(v___x_4002_, 0);
                    lean_inc(v_val_4003_);
                    lean_dec_ref_known(v___x_4002_, 1);
                    v_res_x3f_4004_ = lean_ctor_get(v_val_4003_, 0);
                    lean_inc_ref(v_res_x3f_4004_);
                    v_snap_x3f_4005_ = lean_ctor_get(v_val_4003_, 1);
                    lean_inc(v_snap_x3f_4005_);
                    lean_dec(v_val_4003_);
                    if lean_obj_tag(v_snap_x3f_4005_) == 1 {
                        v_val_4039_ = lean_ctor_get(v_snap_x3f_4005_, 0);
                        lean_inc(v_val_4039_);
                        lean_dec_ref_known(v_snap_x3f_4005_, 1);
                        v___x_4040_ = l_Lean_Syntax_getRange_x3f(v_ref_3981_, v___x_3983_);
                        if lean_obj_tag(v___x_4040_) == 1 {
                            v_val_4041_ = lean_ctor_get(v___x_4040_, 0);
                            lean_inc(v_val_4041_);
                            lean_dec_ref_known(v___x_4040_, 1);
                            v_start_4042_ = lean_ctor_get(v_val_4041_, 0);
                            lean_inc(v_start_4042_);
                            v_stop_4043_ = lean_ctor_get(v_val_4041_, 1);
                            lean_inc(v_stop_4043_);
                            lean_dec(v_val_4041_);
                            lean_inc_ref_n(v_fileMap_3980_, 2);
                            v___x_4044_ = l_Lean_FileMap_toPosition(v_fileMap_3980_, v_start_4042_);
                            lean_dec(v_start_4042_);
                            v___x_4045_ = l_Lean_FileMap_toPosition(v_fileMap_3980_, v_stop_4043_);
                            lean_dec(v_stop_4043_);
                            v___x_4046_ = l___private_Lean_Meta_Basic_0__Lean_Meta_setAllDiagRanges(
                                v_val_4039_,
                                v___x_4044_,
                                v___x_4045_,
                            );
                            v_snap_4024_ = v___x_4046_;
                            v___y_4025_ = v_a_3969_;
                            v___y_4026_ = v_a_3970_;
                            v___y_4027_ = v_a_3971_;
                            v___y_4028_ = v_a_3972_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_4040_);
                            v_snap_4024_ = v_val_4039_;
                            v___y_4025_ = v_a_3969_;
                            v___y_4026_ = v_a_3970_;
                            v___y_4027_ = v_a_3971_;
                            v___y_4028_ = v_a_3972_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_snap_x3f_4005_);
                        v___y_4007_ = v_a_3969_;
                        v___y_4008_ = v_a_3970_;
                        v___y_4009_ = v_a_3971_;
                        v___y_4010_ = v_a_3972_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4002_);
                    lean_del_object(v___x_3999_);
                    lean_dec(v_inst_3965_);
                    v___x_4047_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6_once), _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__6);
                    v___x_4048_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_4047_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_);
                    return v___x_4048_;
                }
            }
            2 => {
                if lean_obj_tag(v_res_x3f_4004_) == 0 {
                    lean_dec(v_inst_3965_);
                    v_a_4011_ = lean_ctor_get(v_res_x3f_4004_, 0);
                    lean_inc(v_a_4011_);
                    lean_dec_ref_known(v_res_x3f_4004_, 1);
                    if v_isShared_4000_ == 0 {
                        lean_ctor_set_tag(v___x_3999_, 1);
                        lean_ctor_set(v___x_3999_, 0, v_a_4011_);
                        v___x_4013_ = v___x_3999_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4011_);
                        v___x_4013_ = v_reuseFailAlloc_4014_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4015_ = lean_ctor_get(v_res_x3f_4004_, 0);
                    lean_inc(v_a_4015_);
                    lean_dec_ref_known(v_res_x3f_4004_, 1);
                    v___x_4016_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                        v_a_4015_,
                        v_inst_3965_,
                    );
                    lean_dec(v_inst_3965_);
                    lean_dec(v_a_4015_);
                    if lean_obj_tag(v___x_4016_) == 0 {
                        lean_del_object(v___x_3999_);
                        v___x_4017_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5_once), _init_l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___closed__5);
                        v___x_4018_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v___x_4017_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
                        return v___x_4018_;
                    } else {
                        v_val_4019_ = lean_ctor_get(v___x_4016_, 0);
                        lean_inc(v_val_4019_);
                        lean_dec_ref_known(v___x_4016_, 1);
                        if v_isShared_4000_ == 0 {
                            lean_ctor_set(v___x_3999_, 0, v_val_4019_);
                            v___x_4021_ = v___x_3999_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_val_4019_);
                            v___x_4021_ = v_reuseFailAlloc_4022_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_4013_;
            }
            4 => {
                return v___x_4021_;
            }
            5 => {
                v___x_4029_ =
                    l_Lean_Language_SnapshotTask_finished___redArg(v___x_3992_, v_snap_4024_);
                v___x_4030_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4029_, v___y_4028_);
                if lean_obj_tag(v___x_4030_) == 0 {
                    lean_dec_ref_known(v___x_4030_, 1);
                    v___y_4007_ = v___y_4025_;
                    v___y_4008_ = v___y_4026_;
                    v___y_4009_ = v___y_4027_;
                    v___y_4010_ = v___y_4028_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_res_x3f_4004_);
                    lean_del_object(v___x_3999_);
                    lean_dec(v_inst_3965_);
                    v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4038_ = (!lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4038_ == 0 {
                        v___x_4033_ = v___x_4030_;
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4031_);
                        lean_dec(v___x_4030_);
                        v___x_4033_ = lean_box(0);
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4034_ == 0 {
                    v___x_4036_ = v___x_4033_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
                    v___x_4036_ = v_reuseFailAlloc_4037_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4036_;
            }
            8 => {
                v___x_4054_ = lean_io_error_to_string(v_a_4050_);
                v___x_4055_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4055_, 0, v___x_4054_);
                v___x_4056_ = l_Lean_MessageData_ofFormat(v___x_4055_);
                lean_inc(v_ref_3981_);
                v___x_4057_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4057_, 0, v_ref_3981_);
                lean_ctor_set(v___x_4057_, 1, v___x_4056_);
                if v_isShared_4053_ == 0 {
                    lean_ctor_set(v___x_4052_, 0, v___x_4057_);
                    v___x_4059_ = v___x_4052_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
                    v___x_4059_ = v_reuseFailAlloc_4060_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg___boxed(
    mut v_inst_4062_: *mut LeanObject,
    mut v_inst_4063_: *mut LeanObject,
    mut v_forConst_4064_: *mut LeanObject,
    mut v_key_4065_: *mut LeanObject,
    mut v_realize_4066_: *mut LeanObject,
    mut v_a_4067_: *mut LeanObject,
    mut v_a_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
    mut v_a_4071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4072_: *mut LeanObject = core::ptr::null_mut();
    v_res_4072_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_4062_, v_inst_4063_, v_forConst_4064_, v_key_4065_, v_realize_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
    lean_dec(v_a_4070_);
    lean_dec_ref(v_a_4069_);
    lean_dec(v_a_4068_);
    lean_dec_ref(v_a_4067_);
    return v_res_4072_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(
    mut v_keys_4073_: *mut LeanObject,
    mut v_vals_4074_: *mut LeanObject,
    mut v_i_4075_: *mut LeanObject,
    mut v_k_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4077_ = lean_array_get_size(v_keys_4073_);
                v___x_4078_ = lean_nat_dec_lt(v_i_4075_, v___x_4077_);
                if v___x_4078_ == 0 {
                    lean_dec(v_i_4075_);
                    v___x_4079_ = lean_box(0);
                    return v___x_4079_;
                } else {
                    v_k_x27_4080_ = lean_array_fget_borrowed(v_keys_4073_, v_i_4075_);
                    v___x_4081_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_k_4076_, v_k_x27_4080_);
                    if v___x_4081_ == 0 {
                        v___x_4082_ = lean_unsigned_to_nat(1);
                        v___x_4083_ = lean_nat_add(v_i_4075_, v___x_4082_);
                        lean_dec(v_i_4075_);
                        v_i_4075_ = v___x_4083_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4085_ = lean_array_fget_borrowed(v_vals_4074_, v_i_4075_);
                        lean_dec(v_i_4075_);
                        lean_inc(v___x_4085_);
                        v___x_4086_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4086_, 0, v___x_4085_);
                        return v___x_4086_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg___boxed(
    mut v_keys_4087_: *mut LeanObject,
    mut v_vals_4088_: *mut LeanObject,
    mut v_i_4089_: *mut LeanObject,
    mut v_k_4090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4091_: *mut LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_4087_, v_vals_4088_, v_i_4089_, v_k_4090_);
    lean_dec_ref(v_k_4090_);
    lean_dec_ref(v_vals_4088_);
    lean_dec_ref(v_keys_4087_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(
    mut v_x_4092_: *mut LeanObject,
    mut v_x_4093_: usize,
    mut v_x_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: usize = 0;
    let mut v___x_4098_: usize = 0;
    let mut v___x_4099_: usize = 0;
    let mut v_j_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: usize = 0;
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4092_) == 0 {
                    v_es_4095_ = lean_ctor_get(v_x_4092_, 0);
                    v___x_4096_ = lean_box(2);
                    v___x_4097_ = 5usize;
                    v___x_4098_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
                    v___x_4099_ = lean_usize_land(v_x_4093_, v___x_4098_);
                    v_j_4100_ = lean_usize_to_nat(v___x_4099_);
                    v___x_4101_ = lean_array_get_borrowed(v___x_4096_, v_es_4095_, v_j_4100_);
                    lean_dec(v_j_4100_);
                    match lean_obj_tag(v___x_4101_) {
                        0 => {
                            v_key_4102_ = lean_ctor_get(v___x_4101_, 0);
                            v_val_4103_ = lean_ctor_get(v___x_4101_, 1);
                            v___x_4104_ =
                                l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_4094_, v_key_4102_);
                            if v___x_4104_ == 0 {
                                v___x_4105_ = lean_box(0);
                                return v___x_4105_;
                            } else {
                                lean_inc(v_val_4103_);
                                v___x_4106_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4106_, 0, v_val_4103_);
                                return v___x_4106_;
                            }
                        }
                        1 => {
                            v_node_4107_ = lean_ctor_get(v___x_4101_, 0);
                            v___x_4108_ = lean_usize_shift_right(v_x_4093_, v___x_4097_);
                            v_x_4092_ = v_node_4107_;
                            v_x_4093_ = v___x_4108_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4110_ = lean_box(0);
                            return v___x_4110_;
                        }
                    }
                } else {
                    v_ks_4111_ = lean_ctor_get(v_x_4092_, 0);
                    v_vs_4112_ = lean_ctor_get(v_x_4092_, 1);
                    v___x_4113_ = lean_unsigned_to_nat(0);
                    v___x_4114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_ks_4111_, v_vs_4112_, v___x_4113_, v_x_4094_);
                    return v___x_4114_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg___boxed(
    mut v_x_4115_: *mut LeanObject,
    mut v_x_4116_: *mut LeanObject,
    mut v_x_4117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14055__boxed_4118_: usize = 0;
    let mut v_res_4119_: *mut LeanObject = core::ptr::null_mut();
    v_x_14055__boxed_4118_ = lean_unbox_usize(v_x_4116_);
    lean_dec(v_x_4116_);
    v_res_4119_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_4115_, v_x_14055__boxed_4118_, v_x_4117_);
    lean_dec_ref(v_x_4117_);
    lean_dec_ref(v_x_4115_);
    return v_res_4119_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(
    mut v_x_4120_: *mut LeanObject,
    mut v_x_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_configKey_4122_: u64 = 0;
    let mut v_expr_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_x3f_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u64 = 0;
    let mut v___y_4127_: u64 = 0;
    let mut v___x_4128_: u64 = 0;
    let mut v___x_4129_: u64 = 0;
    let mut v___x_4130_: usize = 0;
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: u64 = 0;
    let mut v_val_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u64 = 0;
    let mut v___x_4135_: u64 = 0;
    let mut v___x_4136_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_configKey_4122_ = lean_ctor_get_uint64(
                    v_x_4121_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_expr_4123_ = lean_ctor_get(v_x_4121_, 0);
                v_nargs_x3f_4124_ = lean_ctor_get(v_x_4121_, 1);
                v___x_4125_ = l_Lean_Expr_hash(v_expr_4123_);
                if lean_obj_tag(v_nargs_x3f_4124_) == 0 {
                    v___x_4132_ = 11u64;
                    v___y_4127_ = v___x_4132_;
                    state = 1;
                    continue;
                } else {
                    v_val_4133_ = lean_ctor_get(v_nargs_x3f_4124_, 0);
                    v___x_4134_ = lean_uint64_of_nat(v_val_4133_);
                    v___x_4135_ = 13u64;
                    v___x_4136_ = lean_uint64_mix_hash(v___x_4134_, v___x_4135_);
                    v___y_4127_ = v___x_4136_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4128_ = lean_uint64_mix_hash(v___x_4125_, v___y_4127_);
                v___x_4129_ = lean_uint64_mix_hash(v_configKey_4122_, v___x_4128_);
                v___x_4130_ = lean_uint64_to_usize(v___x_4129_);
                v___x_4131_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_4120_, v___x_4130_, v_x_4121_);
                return v___x_4131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg___boxed(
    mut v_x_4137_: *mut LeanObject,
    mut v_x_4138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4139_: *mut LeanObject = core::ptr::null_mut();
    v_res_4139_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_4137_, v_x_4138_);
    lean_dec_ref(v_x_4138_);
    lean_dec_ref(v_x_4137_);
    return v_res_4139_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(
    mut v_x_4140_: *mut LeanObject,
    mut v_x_4141_: *mut LeanObject,
    mut v_x_4142_: *mut LeanObject,
    mut v_x_4143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: u8 = 0;
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4144_ = lean_ctor_get(v_x_4140_, 0);
                v_vs_4145_ = lean_ctor_get(v_x_4140_, 1);
                v_isSharedCheck_4169_ = (!lean_is_exclusive(v_x_4140_)) as u8;
                if v_isSharedCheck_4169_ == 0 {
                    v___x_4147_ = v_x_4140_;
                    v_isShared_4148_ = v_isSharedCheck_4169_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4145_);
                    lean_inc(v_ks_4144_);
                    lean_dec(v_x_4140_);
                    v___x_4147_ = lean_box(0);
                    v_isShared_4148_ = v_isSharedCheck_4169_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4149_ = lean_array_get_size(v_ks_4144_);
                v___x_4150_ = lean_nat_dec_lt(v_x_4141_, v___x_4149_);
                if v___x_4150_ == 0 {
                    lean_dec(v_x_4141_);
                    v___x_4151_ = lean_array_push(v_ks_4144_, v_x_4142_);
                    v___x_4152_ = lean_array_push(v_vs_4145_, v_x_4143_);
                    if v_isShared_4148_ == 0 {
                        lean_ctor_set(v___x_4147_, 1, v___x_4152_);
                        lean_ctor_set(v___x_4147_, 0, v___x_4151_);
                        v___x_4154_ = v___x_4147_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4151_);
                        lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___x_4152_);
                        v___x_4154_ = v_reuseFailAlloc_4155_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4156_ = lean_array_fget_borrowed(v_ks_4144_, v_x_4141_);
                    v___x_4157_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_4142_, v_k_x27_4156_);
                    if v___x_4157_ == 0 {
                        if v_isShared_4148_ == 0 {
                            v___x_4159_ = v___x_4147_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_ks_4144_);
                            lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_vs_4145_);
                            v___x_4159_ = v_reuseFailAlloc_4163_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4164_ = lean_array_fset(v_ks_4144_, v_x_4141_, v_x_4142_);
                        v___x_4165_ = lean_array_fset(v_vs_4145_, v_x_4141_, v_x_4143_);
                        lean_dec(v_x_4141_);
                        if v_isShared_4148_ == 0 {
                            lean_ctor_set(v___x_4147_, 1, v___x_4165_);
                            lean_ctor_set(v___x_4147_, 0, v___x_4164_);
                            v___x_4167_ = v___x_4147_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
                            lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4165_);
                            v___x_4167_ = v_reuseFailAlloc_4168_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4154_;
            }
            3 => {
                v___x_4160_ = lean_unsigned_to_nat(1);
                v___x_4161_ = lean_nat_add(v_x_4141_, v___x_4160_);
                lean_dec(v_x_4141_);
                v_x_4140_ = v___x_4159_;
                v_x_4141_ = v___x_4161_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(
    mut v_n_4170_: *mut LeanObject,
    mut v_k_4171_: *mut LeanObject,
    mut v_v_4172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v___x_4173_ = lean_unsigned_to_nat(0);
    v___x_4174_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_n_4170_, v___x_4173_, v_k_4171_, v_v_4172_);
    return v___x_4174_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    v___x_4175_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4175_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(
    mut v_x_4176_: *mut LeanObject,
    mut v_x_4177_: usize,
    mut v_x_4178_: usize,
    mut v_x_4179_: *mut LeanObject,
    mut v_x_4180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: usize = 0;
    let mut v___x_4183_: usize = 0;
    let mut v___x_4184_: usize = 0;
    let mut v___x_4185_: usize = 0;
    let mut v_j_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4191_: u8 = 0;
    let mut v_v_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4205_: u8 = 0;
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_node_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4217_: usize = 0;
    let mut v___x_4218_: usize = 0;
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4223_: u8 = 0;
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4225_: u8 = 0;
    let mut v_unused_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4231_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4236_: u8 = 0;
    let mut v_ks_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: usize = 0;
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    let mut v_reuseFailAlloc_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4176_) == 0 {
                    v_es_4181_ = lean_ctor_get(v_x_4176_, 0);
                    v___x_4182_ = 5usize;
                    v___x_4183_ = 1usize;
                    v___x_4184_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg___closed__1);
                    v___x_4185_ = lean_usize_land(v_x_4177_, v___x_4184_);
                    v_j_4186_ = lean_usize_to_nat(v___x_4185_);
                    v___x_4187_ = lean_array_get_size(v_es_4181_);
                    v___x_4188_ = lean_nat_dec_lt(v_j_4186_, v___x_4187_);
                    if v___x_4188_ == 0 {
                        lean_dec(v_j_4186_);
                        lean_dec(v_x_4180_);
                        lean_dec_ref(v_x_4179_);
                        return v_x_4176_;
                    } else {
                        lean_inc_ref(v_es_4181_);
                        v_isSharedCheck_4225_ = (!lean_is_exclusive(v_x_4176_)) as u8;
                        if v_isSharedCheck_4225_ == 0 {
                            v_unused_4226_ = lean_ctor_get(v_x_4176_, 0);
                            lean_dec(v_unused_4226_);
                            v___x_4190_ = v_x_4176_;
                            v_isShared_4191_ = v_isSharedCheck_4225_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4176_);
                            v___x_4190_ = lean_box(0);
                            v_isShared_4191_ = v_isSharedCheck_4225_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4227_ = lean_ctor_get(v_x_4176_, 0);
                    v_vs_4228_ = lean_ctor_get(v_x_4176_, 1);
                    v_isSharedCheck_4248_ = (!lean_is_exclusive(v_x_4176_)) as u8;
                    if v_isSharedCheck_4248_ == 0 {
                        v___x_4230_ = v_x_4176_;
                        v_isShared_4231_ = v_isSharedCheck_4248_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4228_);
                        lean_inc(v_ks_4227_);
                        lean_dec(v_x_4176_);
                        v___x_4230_ = lean_box(0);
                        v_isShared_4231_ = v_isSharedCheck_4248_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4192_ = lean_array_fget(v_es_4181_, v_j_4186_);
                v___x_4193_ = lean_box(0);
                v_xs_x27_4194_ = lean_array_fset(v_es_4181_, v_j_4186_, v___x_4193_);
                match lean_obj_tag(v_v_4192_) {
                    0 => {
                        v_key_4201_ = lean_ctor_get(v_v_4192_, 0);
                        v_val_4202_ = lean_ctor_get(v_v_4192_, 1);
                        v_isSharedCheck_4212_ = (!lean_is_exclusive(v_v_4192_)) as u8;
                        if v_isSharedCheck_4212_ == 0 {
                            v___x_4204_ = v_v_4192_;
                            v_isShared_4205_ = v_isSharedCheck_4212_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4202_);
                            lean_inc(v_key_4201_);
                            lean_dec(v_v_4192_);
                            v___x_4204_ = lean_box(0);
                            v_isShared_4205_ = v_isSharedCheck_4212_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4213_ = lean_ctor_get(v_v_4192_, 0);
                        v_isSharedCheck_4223_ = (!lean_is_exclusive(v_v_4192_)) as u8;
                        if v_isSharedCheck_4223_ == 0 {
                            v___x_4215_ = v_v_4192_;
                            v_isShared_4216_ = v_isSharedCheck_4223_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4213_);
                            lean_dec(v_v_4192_);
                            v___x_4215_ = lean_box(0);
                            v_isShared_4216_ = v_isSharedCheck_4223_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4224_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4224_, 0, v_x_4179_);
                        lean_ctor_set(v___x_4224_, 1, v_x_4180_);
                        v___y_4196_ = v___x_4224_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4197_ = lean_array_fset(v_xs_x27_4194_, v_j_4186_, v___y_4196_);
                lean_dec(v_j_4186_);
                if v_isShared_4191_ == 0 {
                    lean_ctor_set(v___x_4190_, 0, v___x_4197_);
                    v___x_4199_ = v___x_4190_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4197_);
                    v___x_4199_ = v_reuseFailAlloc_4200_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4199_;
            }
            4 => {
                v___x_4206_ = l_Lean_Meta_instBEqInfoCacheKey_beq(v_x_4179_, v_key_4201_);
                if v___x_4206_ == 0 {
                    lean_del_object(v___x_4204_);
                    v___x_4207_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4201_,
                        v_val_4202_,
                        v_x_4179_,
                        v_x_4180_,
                    );
                    v___x_4208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4208_, 0, v___x_4207_);
                    v___y_4196_ = v___x_4208_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4202_);
                    lean_dec(v_key_4201_);
                    if v_isShared_4205_ == 0 {
                        lean_ctor_set(v___x_4204_, 1, v_x_4180_);
                        lean_ctor_set(v___x_4204_, 0, v_x_4179_);
                        v___x_4210_ = v___x_4204_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_x_4179_);
                        lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_x_4180_);
                        v___x_4210_ = v_reuseFailAlloc_4211_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4196_ = v___x_4210_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4217_ = lean_usize_shift_right(v_x_4177_, v___x_4182_);
                v___x_4218_ = lean_usize_add(v_x_4178_, v___x_4183_);
                v___x_4219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_node_4213_, v___x_4217_, v___x_4218_, v_x_4179_, v_x_4180_);
                if v_isShared_4216_ == 0 {
                    lean_ctor_set(v___x_4215_, 0, v___x_4219_);
                    v___x_4221_ = v___x_4215_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
                    v___x_4221_ = v_reuseFailAlloc_4222_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4196_ = v___x_4221_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4231_ == 0 {
                    v___x_4233_ = v___x_4230_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_ks_4227_);
                    lean_ctor_set(v_reuseFailAlloc_4247_, 1, v_vs_4228_);
                    v___x_4233_ = v_reuseFailAlloc_4247_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4234_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v___x_4233_, v_x_4179_, v_x_4180_);
                v___x_4242_ = 7usize;
                v___x_4243_ = lean_usize_dec_le(v___x_4242_, v_x_4178_);
                if v___x_4243_ == 0 {
                    v___x_4244_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4234_);
                    v___x_4245_ = lean_unsigned_to_nat(4);
                    v___x_4246_ = lean_nat_dec_lt(v___x_4244_, v___x_4245_);
                    lean_dec(v___x_4244_);
                    v___y_4236_ = v___x_4246_;
                    state = 10;
                    continue;
                } else {
                    v___y_4236_ = v___x_4243_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4236_ == 0 {
                    v_ks_4237_ = lean_ctor_get(v_newNode_4234_, 0);
                    lean_inc_ref(v_ks_4237_);
                    v_vs_4238_ = lean_ctor_get(v_newNode_4234_, 1);
                    lean_inc_ref(v_vs_4238_);
                    lean_dec_ref(v_newNode_4234_);
                    v___x_4239_ = lean_unsigned_to_nat(0);
                    v___x_4240_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___closed__0);
                    v___x_4241_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_x_4178_, v_ks_4237_, v_vs_4238_, v___x_4239_, v___x_4240_);
                    lean_dec_ref(v_vs_4238_);
                    lean_dec_ref(v_ks_4237_);
                    return v___x_4241_;
                } else {
                    return v_newNode_4234_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(
    mut v_depth_4249_: usize,
    mut v_keys_4250_: *mut LeanObject,
    mut v_vals_4251_: *mut LeanObject,
    mut v_i_4252_: *mut LeanObject,
    mut v_entries_4253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut v_k_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_configKey_4257_: u64 = 0;
    let mut v_expr_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_x3f_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: u64 = 0;
    let mut v___y_4263_: u64 = 0;
    let mut v___x_4264_: u64 = 0;
    let mut v___x_4265_: u64 = 0;
    let mut v_h_4266_: usize = 0;
    let mut v___x_4267_: usize = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: usize = 0;
    let mut v___x_4270_: usize = 0;
    let mut v___x_4271_: usize = 0;
    let mut v_h_4272_: usize = 0;
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u64 = 0;
    let mut v_val_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: u64 = 0;
    let mut v___x_4279_: u64 = 0;
    let mut v___x_4280_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4254_ = lean_array_get_size(v_keys_4250_);
                v___x_4255_ = lean_nat_dec_lt(v_i_4252_, v___x_4254_);
                if v___x_4255_ == 0 {
                    lean_dec(v_i_4252_);
                    return v_entries_4253_;
                } else {
                    v_k_4256_ = lean_array_fget_borrowed(v_keys_4250_, v_i_4252_);
                    v_configKey_4257_ = lean_ctor_get_uint64(
                        v_k_4256_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_expr_4258_ = lean_ctor_get(v_k_4256_, 0);
                    v_nargs_x3f_4259_ = lean_ctor_get(v_k_4256_, 1);
                    v_v_4260_ = lean_array_fget_borrowed(v_vals_4251_, v_i_4252_);
                    v___x_4261_ = l_Lean_Expr_hash(v_expr_4258_);
                    if lean_obj_tag(v_nargs_x3f_4259_) == 0 {
                        v___x_4276_ = 11u64;
                        v___y_4263_ = v___x_4276_;
                        state = 1;
                        continue;
                    } else {
                        v_val_4277_ = lean_ctor_get(v_nargs_x3f_4259_, 0);
                        v___x_4278_ = lean_uint64_of_nat(v_val_4277_);
                        v___x_4279_ = 13u64;
                        v___x_4280_ = lean_uint64_mix_hash(v___x_4278_, v___x_4279_);
                        v___y_4263_ = v___x_4280_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4264_ = lean_uint64_mix_hash(v___x_4261_, v___y_4263_);
                v___x_4265_ = lean_uint64_mix_hash(v_configKey_4257_, v___x_4264_);
                v_h_4266_ = lean_uint64_to_usize(v___x_4265_);
                v___x_4267_ = 5usize;
                v___x_4268_ = lean_unsigned_to_nat(1);
                v___x_4269_ = 1usize;
                v___x_4270_ = lean_usize_sub(v_depth_4249_, v___x_4269_);
                v___x_4271_ = lean_usize_mul(v___x_4267_, v___x_4270_);
                v_h_4272_ = lean_usize_shift_right(v_h_4266_, v___x_4271_);
                v___x_4273_ = lean_nat_add(v_i_4252_, v___x_4268_);
                lean_dec(v_i_4252_);
                lean_inc(v_v_4260_);
                lean_inc(v_k_4256_);
                v___x_4274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_entries_4253_, v_h_4272_, v_depth_4249_, v_k_4256_, v_v_4260_);
                v_i_4252_ = v___x_4273_;
                v_entries_4253_ = v___x_4274_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg___boxed(
    mut v_depth_4281_: *mut LeanObject,
    mut v_keys_4282_: *mut LeanObject,
    mut v_vals_4283_: *mut LeanObject,
    mut v_i_4284_: *mut LeanObject,
    mut v_entries_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4286_: usize = 0;
    let mut v_res_4287_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4286_ = lean_unbox_usize(v_depth_4281_);
    lean_dec(v_depth_4281_);
    v_res_4287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_boxed_4286_, v_keys_4282_, v_vals_4283_, v_i_4284_, v_entries_4285_);
    lean_dec_ref(v_vals_4283_);
    lean_dec_ref(v_keys_4282_);
    return v_res_4287_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg___boxed(
    mut v_x_4288_: *mut LeanObject,
    mut v_x_4289_: *mut LeanObject,
    mut v_x_4290_: *mut LeanObject,
    mut v_x_4291_: *mut LeanObject,
    mut v_x_4292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14234__boxed_4293_: usize = 0;
    let mut v_x_14235__boxed_4294_: usize = 0;
    let mut v_res_4295_: *mut LeanObject = core::ptr::null_mut();
    v_x_14234__boxed_4293_ = lean_unbox_usize(v_x_4289_);
    lean_dec(v_x_4289_);
    v_x_14235__boxed_4294_ = lean_unbox_usize(v_x_4290_);
    lean_dec(v_x_4290_);
    v_res_4295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_4288_, v_x_14234__boxed_4293_, v_x_14235__boxed_4294_, v_x_4291_, v_x_4292_);
    return v_res_4295_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(
    mut v_x_4296_: *mut LeanObject,
    mut v_x_4297_: *mut LeanObject,
    mut v_x_4298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_configKey_4299_: u64 = 0;
    let mut v_expr_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_x3f_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: u64 = 0;
    let mut v___y_4304_: u64 = 0;
    let mut v___x_4305_: u64 = 0;
    let mut v___x_4306_: u64 = 0;
    let mut v___x_4307_: usize = 0;
    let mut v___x_4308_: usize = 0;
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u64 = 0;
    let mut v_val_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: u64 = 0;
    let mut v___x_4313_: u64 = 0;
    let mut v___x_4314_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_configKey_4299_ = lean_ctor_get_uint64(
                    v_x_4297_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_expr_4300_ = lean_ctor_get(v_x_4297_, 0);
                v_nargs_x3f_4301_ = lean_ctor_get(v_x_4297_, 1);
                v___x_4302_ = l_Lean_Expr_hash(v_expr_4300_);
                if lean_obj_tag(v_nargs_x3f_4301_) == 0 {
                    v___x_4310_ = 11u64;
                    v___y_4304_ = v___x_4310_;
                    state = 1;
                    continue;
                } else {
                    v_val_4311_ = lean_ctor_get(v_nargs_x3f_4301_, 0);
                    v___x_4312_ = lean_uint64_of_nat(v_val_4311_);
                    v___x_4313_ = 13u64;
                    v___x_4314_ = lean_uint64_mix_hash(v___x_4312_, v___x_4313_);
                    v___y_4304_ = v___x_4314_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4305_ = lean_uint64_mix_hash(v___x_4302_, v___y_4304_);
                v___x_4306_ = lean_uint64_mix_hash(v_configKey_4299_, v___x_4305_);
                v___x_4307_ = lean_uint64_to_usize(v___x_4306_);
                v___x_4308_ = 1usize;
                v___x_4309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_4296_, v___x_4307_, v___x_4308_, v_x_4297_, v_x_4298_);
                return v___x_4309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(
    mut v_x_4315_: *mut LeanObject,
) -> u8 {
    let mut v___x_4316_: u8 = 0;
    let mut v_head_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4315_) == 0 {
                    v___x_4316_ = 0;
                    return v___x_4316_;
                } else {
                    v_head_4317_ = lean_ctor_get(v_x_4315_, 0);
                    v_tail_4318_ = lean_ctor_get(v_x_4315_, 1);
                    v___x_4319_ = l_Lean_Level_hasMVar(v_head_4317_);
                    if v___x_4319_ == 0 {
                        v_x_4315_ = v_tail_4318_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4319_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___boxed(
    mut v_x_4321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4322_: u8 = 0;
    let mut v_r_4323_: *mut LeanObject = core::ptr::null_mut();
    v_res_4322_ =
        l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(
            v_x_4321_,
        );
    lean_dec(v_x_4321_);
    v_r_4323_ = lean_box((v_res_4322_) as usize);
    return v_r_4323_;
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(
    mut v_fn_4326_: *mut LeanObject,
    mut v_maxArgs_x3f_4327_: *mut LeanObject,
    mut v_a_4328_: *mut LeanObject,
    mut v_a_4329_: *mut LeanObject,
    mut v_a_4330_: *mut LeanObject,
    mut v_a_4331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4337_: u8 = 0;
    let mut v_finfo_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v_inferType_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funInfo_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_whnf_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqTrans_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqPerm_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funInfo_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_a_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_maxArgs_x3f_4327_);
                lean_inc_ref(v_fn_4326_);
                v___x_4333_ =
                    l_Lean_Meta_mkInfoCacheKey___redArg(v_fn_4326_, v_maxArgs_x3f_4327_, v_a_4328_);
                if lean_obj_tag(v___x_4333_) == 0 {
                    v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
                    v_isSharedCheck_4398_ = (!lean_is_exclusive(v___x_4333_)) as u8;
                    if v_isSharedCheck_4398_ == 0 {
                        v___x_4336_ = v___x_4333_;
                        v_isShared_4337_ = v_isSharedCheck_4398_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4334_);
                        lean_dec(v___x_4333_);
                        v___x_4336_ = lean_box(0);
                        v_isShared_4337_ = v_isSharedCheck_4398_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_maxArgs_x3f_4327_);
                    lean_dec_ref(v_fn_4326_);
                    v_a_4399_ = lean_ctor_get(v___x_4333_, 0);
                    v_isSharedCheck_4406_ = (!lean_is_exclusive(v___x_4333_)) as u8;
                    if v_isSharedCheck_4406_ == 0 {
                        v___x_4401_ = v___x_4333_;
                        v_isShared_4402_ = v_isSharedCheck_4406_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4399_);
                        lean_dec(v___x_4333_);
                        v___x_4401_ = lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4406_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4372_ = lean_st_ref_get(v_a_4329_);
                v_cache_4373_ = lean_ctor_get(v___x_4372_, 1);
                lean_inc_ref(v_cache_4373_);
                lean_dec(v___x_4372_);
                v_funInfo_4374_ = lean_ctor_get(v_cache_4373_, 1);
                lean_inc_ref(v_funInfo_4374_);
                lean_dec_ref(v_cache_4373_);
                v___x_4375_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_funInfo_4374_, v_a_4334_);
                lean_dec_ref(v_funInfo_4374_);
                if lean_obj_tag(v___x_4375_) == 0 {
                    v___f_4376_ =
                        l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__0;
                    lean_inc(v_maxArgs_x3f_4327_);
                    lean_inc_ref(v_fn_4326_);
                    v___f_4377_ = lean_alloc_closure(
                        l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1___boxed
                            as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    lean_closure_set(v___f_4377_, 0, v_fn_4326_);
                    lean_closure_set(v___f_4377_, 1, v_maxArgs_x3f_4327_);
                    lean_closure_set(v___f_4377_, 2, v___f_4376_);
                    if lean_obj_tag(v_fn_4326_) == 4 {
                        v_declName_4378_ = lean_ctor_get(v_fn_4326_, 0);
                        v_us_4379_ = lean_ctor_get(v_fn_4326_, 1);
                        v___x_4380_ = l_List_any___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(v_us_4379_);
                        if v___x_4380_ == 0 {
                            lean_inc(v_us_4379_);
                            lean_inc_n(v_declName_4378_, 2);
                            lean_dec_ref_known(v_fn_4326_, 2);
                            v___x_4381_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_instImpl_00___x40_Lean_Meta_FunInfo_117766202____hygCtx___hyg_63_;
                            v___x_4382_ = l_Lean_Meta_instImpl_00___x40_Lean_Meta_Basic_383016249____hygCtx___hyg_24_;
                            v___x_4383_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_4383_, 0, v_declName_4378_);
                            lean_ctor_set(v___x_4383_, 1, v_us_4379_);
                            lean_ctor_set(v___x_4383_, 2, v_maxArgs_x3f_4327_);
                            v___x_4384_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v___x_4381_, v___x_4382_, v_declName_4378_, v___x_4383_, v___f_4377_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
                            if lean_obj_tag(v___x_4384_) == 0 {
                                v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
                                lean_inc(v_a_4385_);
                                lean_dec_ref_known(v___x_4384_, 1);
                                v_finfo_4339_ = v_a_4385_;
                                v___y_4340_ = v_a_4329_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_4336_);
                                lean_dec(v_a_4334_);
                                return v___x_4384_;
                            }
                        } else {
                            lean_dec_ref(v___f_4377_);
                            lean_inc(v_a_4331_);
                            lean_inc_ref(v_a_4330_);
                            lean_inc(v_a_4329_);
                            lean_inc_ref(v_a_4328_);
                            v___x_4386_ =
                                l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(
                                    v_fn_4326_,
                                    v_maxArgs_x3f_4327_,
                                    v___f_4376_,
                                    v_a_4328_,
                                    v_a_4329_,
                                    v_a_4330_,
                                    v_a_4331_,
                                );
                            if lean_obj_tag(v___x_4386_) == 0 {
                                v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
                                lean_inc(v_a_4387_);
                                lean_dec_ref_known(v___x_4386_, 1);
                                v_finfo_4339_ = v_a_4387_;
                                v___y_4340_ = v_a_4329_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_4336_);
                                lean_dec(v_a_4334_);
                                return v___x_4386_;
                            }
                        }
                    } else {
                        lean_dec_ref(v___f_4377_);
                        lean_inc(v_a_4331_);
                        lean_inc_ref(v_a_4330_);
                        lean_inc(v_a_4329_);
                        lean_inc_ref(v_a_4328_);
                        v___x_4388_ =
                            l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__1(
                                v_fn_4326_,
                                v_maxArgs_x3f_4327_,
                                v___f_4376_,
                                v_a_4328_,
                                v_a_4329_,
                                v_a_4330_,
                                v_a_4331_,
                            );
                        if lean_obj_tag(v___x_4388_) == 0 {
                            v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
                            lean_inc(v_a_4389_);
                            lean_dec_ref_known(v___x_4388_, 1);
                            v_finfo_4339_ = v_a_4389_;
                            v___y_4340_ = v_a_4329_;
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_4336_);
                            lean_dec(v_a_4334_);
                            return v___x_4388_;
                        }
                    }
                } else {
                    lean_del_object(v___x_4336_);
                    lean_dec(v_a_4334_);
                    lean_dec(v_maxArgs_x3f_4327_);
                    lean_dec_ref(v_fn_4326_);
                    v_val_4390_ = lean_ctor_get(v___x_4375_, 0);
                    v_isSharedCheck_4397_ = (!lean_is_exclusive(v___x_4375_)) as u8;
                    if v_isSharedCheck_4397_ == 0 {
                        v___x_4392_ = v___x_4375_;
                        v_isShared_4393_ = v_isSharedCheck_4397_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_4390_);
                        lean_dec(v___x_4375_);
                        v___x_4392_ = lean_box(0);
                        v_isShared_4393_ = v_isSharedCheck_4397_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4341_ = lean_st_ref_take(v___y_4340_);
                v_cache_4342_ = lean_ctor_get(v___x_4341_, 1);
                v_mctx_4343_ = lean_ctor_get(v___x_4341_, 0);
                v_zetaDeltaFVarIds_4344_ = lean_ctor_get(v___x_4341_, 2);
                v_postponed_4345_ = lean_ctor_get(v___x_4341_, 3);
                v_diag_4346_ = lean_ctor_get(v___x_4341_, 4);
                v_isSharedCheck_4371_ = (!lean_is_exclusive(v___x_4341_)) as u8;
                if v_isSharedCheck_4371_ == 0 {
                    v___x_4348_ = v___x_4341_;
                    v_isShared_4349_ = v_isSharedCheck_4371_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_4346_);
                    lean_inc(v_postponed_4345_);
                    lean_inc(v_zetaDeltaFVarIds_4344_);
                    lean_inc(v_cache_4342_);
                    lean_inc(v_mctx_4343_);
                    lean_dec(v___x_4341_);
                    v___x_4348_ = lean_box(0);
                    v_isShared_4349_ = v_isSharedCheck_4371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_inferType_4350_ = lean_ctor_get(v_cache_4342_, 0);
                v_funInfo_4351_ = lean_ctor_get(v_cache_4342_, 1);
                v_synthInstance_4352_ = lean_ctor_get(v_cache_4342_, 2);
                v_whnf_4353_ = lean_ctor_get(v_cache_4342_, 3);
                v_defEqTrans_4354_ = lean_ctor_get(v_cache_4342_, 4);
                v_defEqPerm_4355_ = lean_ctor_get(v_cache_4342_, 5);
                v_isSharedCheck_4370_ = (!lean_is_exclusive(v_cache_4342_)) as u8;
                if v_isSharedCheck_4370_ == 0 {
                    v___x_4357_ = v_cache_4342_;
                    v_isShared_4358_ = v_isSharedCheck_4370_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_defEqPerm_4355_);
                    lean_inc(v_defEqTrans_4354_);
                    lean_inc(v_whnf_4353_);
                    lean_inc(v_synthInstance_4352_);
                    lean_inc(v_funInfo_4351_);
                    lean_inc(v_inferType_4350_);
                    lean_dec(v_cache_4342_);
                    v___x_4357_ = lean_box(0);
                    v_isShared_4358_ = v_isSharedCheck_4370_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v_finfo_4339_);
                v___x_4359_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_funInfo_4351_, v_a_4334_, v_finfo_4339_);
                if v_isShared_4358_ == 0 {
                    lean_ctor_set(v___x_4357_, 1, v___x_4359_);
                    v___x_4361_ = v___x_4357_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_inferType_4350_);
                    lean_ctor_set(v_reuseFailAlloc_4369_, 1, v___x_4359_);
                    lean_ctor_set(v_reuseFailAlloc_4369_, 2, v_synthInstance_4352_);
                    lean_ctor_set(v_reuseFailAlloc_4369_, 3, v_whnf_4353_);
                    lean_ctor_set(v_reuseFailAlloc_4369_, 4, v_defEqTrans_4354_);
                    lean_ctor_set(v_reuseFailAlloc_4369_, 5, v_defEqPerm_4355_);
                    v___x_4361_ = v_reuseFailAlloc_4369_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4349_ == 0 {
                    lean_ctor_set(v___x_4348_, 1, v___x_4361_);
                    v___x_4363_ = v___x_4348_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_mctx_4343_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 1, v___x_4361_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 2, v_zetaDeltaFVarIds_4344_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 3, v_postponed_4345_);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 4, v_diag_4346_);
                    v___x_4363_ = v_reuseFailAlloc_4368_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4364_ = lean_st_ref_set(v___y_4340_, v___x_4363_);
                if v_isShared_4337_ == 0 {
                    lean_ctor_set(v___x_4336_, 0, v_finfo_4339_);
                    v___x_4366_ = v___x_4336_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_finfo_4339_);
                    v___x_4366_ = v_reuseFailAlloc_4367_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4366_;
            }
            8 => {
                if v_isShared_4393_ == 0 {
                    lean_ctor_set_tag(v___x_4392_, 0);
                    v___x_4395_ = v___x_4392_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_val_4390_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4395_;
            }
            10 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___boxed(
    mut v_fn_4407_: *mut LeanObject,
    mut v_maxArgs_x3f_4408_: *mut LeanObject,
    mut v_a_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
    mut v_a_4413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4414_: *mut LeanObject = core::ptr::null_mut();
    v_res_4414_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(
        v_fn_4407_,
        v_maxArgs_x3f_4408_,
        v_a_4409_,
        v_a_4410_,
        v_a_4411_,
        v_a_4412_,
    );
    lean_dec(v_a_4412_);
    lean_dec_ref(v_a_4411_);
    lean_dec(v_a_4410_);
    lean_dec_ref(v_a_4409_);
    return v_res_4414_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(
    mut v_00_u03b2_4415_: *mut LeanObject,
    mut v_k_4416_: *mut LeanObject,
    mut v_t_4417_: *mut LeanObject,
) -> u8 {
    let mut v___x_4418_: u8 = 0;
    v___x_4418_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(v_k_4416_, v_t_4417_);
    return v___x_4418_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(
    mut v_00_u03b2_4419_: *mut LeanObject,
    mut v_k_4420_: *mut LeanObject,
    mut v_t_4421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4422_: u8 = 0;
    let mut v_r_4423_: *mut LeanObject = core::ptr::null_mut();
    v_res_4422_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(v_00_u03b2_4419_, v_k_4420_, v_t_4421_);
    lean_dec(v_t_4421_);
    lean_dec(v_k_4420_);
    v_r_4423_ = lean_box((v_res_4422_) as usize);
    return v_r_4423_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(
    mut v_upperBound_4424_: *mut LeanObject,
    mut v_val_4425_: *mut LeanObject,
    mut v___x_4426_: *mut LeanObject,
    mut v_fvars_4427_: *mut LeanObject,
    mut v___y_4428_: u8,
    mut v_inst_4429_: *mut LeanObject,
    mut v_R_4430_: *mut LeanObject,
    mut v_a_4431_: *mut LeanObject,
    mut v_b_4432_: *mut LeanObject,
    mut v_c_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    v___x_4439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___redArg(v_upperBound_4424_, v_val_4425_, v___x_4426_, v_fvars_4427_, v___y_4428_, v_a_4431_, v_b_4432_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
    return v___x_4439_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2___boxed(
    mut v_upperBound_4440_: *mut LeanObject,
    mut v_val_4441_: *mut LeanObject,
    mut v___x_4442_: *mut LeanObject,
    mut v_fvars_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v_inst_4445_: *mut LeanObject,
    mut v_R_4446_: *mut LeanObject,
    mut v_a_4447_: *mut LeanObject,
    mut v_b_4448_: *mut LeanObject,
    mut v_c_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_14589__boxed_4455_: u8 = 0;
    let mut v_res_4456_: *mut LeanObject = core::ptr::null_mut();
    v___y_14589__boxed_4455_ = (lean_unbox(v___y_4444_) as u8);
    v_res_4456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__2(v_upperBound_4440_, v_val_4441_, v___x_4442_, v_fvars_4443_, v___y_14589__boxed_4455_, v_inst_4445_, v_R_4446_, v_a_4447_, v_b_4448_, v_c_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
    lean_dec(v___y_4453_);
    lean_dec_ref(v___y_4452_);
    lean_dec(v___y_4451_);
    lean_dec_ref(v___y_4450_);
    lean_dec_ref(v_fvars_4443_);
    lean_dec_ref(v___x_4442_);
    lean_dec_ref(v_val_4441_);
    lean_dec(v_upperBound_4440_);
    return v_res_4456_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(
    mut v_upperBound_4457_: *mut LeanObject,
    mut v_fvars_4458_: *mut LeanObject,
    mut v_inst_4459_: *mut LeanObject,
    mut v_R_4460_: *mut LeanObject,
    mut v_a_4461_: *mut LeanObject,
    mut v_b_4462_: *mut LeanObject,
    mut v_c_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
    mut v___y_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    v___x_4469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___redArg(v_upperBound_4457_, v_fvars_4458_, v_a_4461_, v_b_4462_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
    return v___x_4469_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4___boxed(
    mut v_upperBound_4470_: *mut LeanObject,
    mut v_fvars_4471_: *mut LeanObject,
    mut v_inst_4472_: *mut LeanObject,
    mut v_R_4473_: *mut LeanObject,
    mut v_a_4474_: *mut LeanObject,
    mut v_b_4475_: *mut LeanObject,
    mut v_c_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
    mut v___y_4481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4482_: *mut LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__4(v_upperBound_4470_, v_fvars_4471_, v_inst_4472_, v_R_4473_, v_a_4474_, v_b_4475_, v_c_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
    lean_dec(v___y_4480_);
    lean_dec_ref(v___y_4479_);
    lean_dec(v___y_4478_);
    lean_dec_ref(v___y_4477_);
    lean_dec_ref(v_fvars_4471_);
    lean_dec(v_upperBound_4470_);
    return v_res_4482_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6(
    mut v_00_u03b2_4483_: *mut LeanObject,
    mut v_x_4484_: *mut LeanObject,
    mut v_x_4485_: *mut LeanObject,
    mut v_x_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    v___x_4487_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6___redArg(v_x_4484_, v_x_4485_, v_x_4486_);
    return v___x_4487_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(
    mut v_00_u03b2_4488_: *mut LeanObject,
    mut v_x_4489_: *mut LeanObject,
    mut v_x_4490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    v___x_4491_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___redArg(v_x_4489_, v_x_4490_);
    return v___x_4491_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7___boxed(
    mut v_00_u03b2_4492_: *mut LeanObject,
    mut v_x_4493_: *mut LeanObject,
    mut v_x_4494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4495_: *mut LeanObject = core::ptr::null_mut();
    v_res_4495_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7(v_00_u03b2_4492_, v_x_4493_, v_x_4494_);
    lean_dec_ref(v_x_4494_);
    lean_dec_ref(v_x_4493_);
    return v_res_4495_;
}
pub unsafe fn l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(
    mut v_00_u03b2_4496_: *mut LeanObject,
    mut v_msg_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    v___x_4503_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___redArg(v_msg_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
    return v___x_4503_;
}
pub unsafe fn l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12___boxed(
    mut v_00_u03b2_4504_: *mut LeanObject,
    mut v_msg_4505_: *mut LeanObject,
    mut v___y_4506_: *mut LeanObject,
    mut v___y_4507_: *mut LeanObject,
    mut v___y_4508_: *mut LeanObject,
    mut v___y_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4511_: *mut LeanObject = core::ptr::null_mut();
    v_res_4511_ = l_panic___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__12(v_00_u03b2_4504_, v_msg_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
    lean_dec(v___y_4509_);
    lean_dec_ref(v___y_4508_);
    lean_dec(v___y_4507_);
    lean_dec_ref(v___y_4506_);
    return v_res_4511_;
}
pub unsafe fn l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(
    mut v_00_u03b2_4512_: *mut LeanObject,
    mut v_inst_4513_: *mut LeanObject,
    mut v_inst_4514_: *mut LeanObject,
    mut v_forConst_4515_: *mut LeanObject,
    mut v_key_4516_: *mut LeanObject,
    mut v_realize_4517_: *mut LeanObject,
    mut v_a_4518_: *mut LeanObject,
    mut v_a_4519_: *mut LeanObject,
    mut v_a_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    v___x_4523_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___redArg(v_inst_4513_, v_inst_4514_, v_forConst_4515_, v_key_4516_, v_realize_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
    return v___x_4523_;
}
pub unsafe fn l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9___boxed(
    mut v_00_u03b2_4524_: *mut LeanObject,
    mut v_inst_4525_: *mut LeanObject,
    mut v_inst_4526_: *mut LeanObject,
    mut v_forConst_4527_: *mut LeanObject,
    mut v_key_4528_: *mut LeanObject,
    mut v_realize_4529_: *mut LeanObject,
    mut v_a_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
    mut v_a_4532_: *mut LeanObject,
    mut v_a_4533_: *mut LeanObject,
    mut v_a_4534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4535_: *mut LeanObject = core::ptr::null_mut();
    v_res_4535_ = l_Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9(v_00_u03b2_4524_, v_inst_4525_, v_inst_4526_, v_forConst_4527_, v_key_4528_, v_realize_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
    lean_dec(v_a_4533_);
    lean_dec_ref(v_a_4532_);
    lean_dec(v_a_4531_);
    lean_dec_ref(v_a_4530_);
    return v_res_4535_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(
    mut v_00_u03b2_4536_: *mut LeanObject,
    mut v_x_4537_: *mut LeanObject,
    mut v_x_4538_: usize,
    mut v_x_4539_: usize,
    mut v_x_4540_: *mut LeanObject,
    mut v_x_4541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    v___x_4542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___redArg(v_x_4537_, v_x_4538_, v_x_4539_, v_x_4540_, v_x_4541_);
    return v___x_4542_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6___boxed(
    mut v_00_u03b2_4543_: *mut LeanObject,
    mut v_x_4544_: *mut LeanObject,
    mut v_x_4545_: *mut LeanObject,
    mut v_x_4546_: *mut LeanObject,
    mut v_x_4547_: *mut LeanObject,
    mut v_x_4548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14686__boxed_4549_: usize = 0;
    let mut v_x_14687__boxed_4550_: usize = 0;
    let mut v_res_4551_: *mut LeanObject = core::ptr::null_mut();
    v_x_14686__boxed_4549_ = lean_unbox_usize(v_x_4545_);
    lean_dec(v_x_4545_);
    v_x_14687__boxed_4550_ = lean_unbox_usize(v_x_4546_);
    lean_dec(v_x_4546_);
    v_res_4551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6(v_00_u03b2_4543_, v_x_4544_, v_x_14686__boxed_4549_, v_x_14687__boxed_4550_, v_x_4547_, v_x_4548_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(
    mut v_00_u03b2_4552_: *mut LeanObject,
    mut v_x_4553_: *mut LeanObject,
    mut v_x_4554_: usize,
    mut v_x_4555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    v___x_4556_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___redArg(v_x_4553_, v_x_4554_, v_x_4555_);
    return v___x_4556_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8___boxed(
    mut v_00_u03b2_4557_: *mut LeanObject,
    mut v_x_4558_: *mut LeanObject,
    mut v_x_4559_: *mut LeanObject,
    mut v_x_4560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14703__boxed_4561_: usize = 0;
    let mut v_res_4562_: *mut LeanObject = core::ptr::null_mut();
    v_x_14703__boxed_4561_ = lean_unbox_usize(v_x_4559_);
    lean_dec(v_x_4559_);
    v_res_4562_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8(v_00_u03b2_4557_, v_x_4558_, v_x_14703__boxed_4561_, v_x_4560_);
    lean_dec_ref(v_x_4560_);
    lean_dec_ref(v_x_4558_);
    return v_res_4562_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7(
    mut v_00_u03b2_4563_: *mut LeanObject,
    mut v_n_4564_: *mut LeanObject,
    mut v_k_4565_: *mut LeanObject,
    mut v_v_4566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    v___x_4567_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7___redArg(v_n_4564_, v_k_4565_, v_v_4566_);
    return v___x_4567_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(
    mut v_00_u03b2_4568_: *mut LeanObject,
    mut v_depth_4569_: usize,
    mut v_keys_4570_: *mut LeanObject,
    mut v_vals_4571_: *mut LeanObject,
    mut v_heq_4572_: *mut LeanObject,
    mut v_i_4573_: *mut LeanObject,
    mut v_entries_4574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    v___x_4575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___redArg(v_depth_4569_, v_keys_4570_, v_vals_4571_, v_i_4573_, v_entries_4574_);
    return v___x_4575_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8___boxed(
    mut v_00_u03b2_4576_: *mut LeanObject,
    mut v_depth_4577_: *mut LeanObject,
    mut v_keys_4578_: *mut LeanObject,
    mut v_vals_4579_: *mut LeanObject,
    mut v_heq_4580_: *mut LeanObject,
    mut v_i_4581_: *mut LeanObject,
    mut v_entries_4582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4583_: usize = 0;
    let mut v_res_4584_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4583_ = lean_unbox_usize(v_depth_4577_);
    lean_dec(v_depth_4577_);
    v_res_4584_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__8(v_00_u03b2_4576_, v_depth_boxed_4583_, v_keys_4578_, v_vals_4579_, v_heq_4580_, v_i_4581_, v_entries_4582_);
    lean_dec_ref(v_vals_4579_);
    lean_dec_ref(v_keys_4578_);
    return v_res_4584_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(
    mut v_00_u03b2_4585_: *mut LeanObject,
    mut v_keys_4586_: *mut LeanObject,
    mut v_vals_4587_: *mut LeanObject,
    mut v_heq_4588_: *mut LeanObject,
    mut v_i_4589_: *mut LeanObject,
    mut v_k_4590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    v___x_4591_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___redArg(v_keys_4586_, v_vals_4587_, v_i_4589_, v_k_4590_);
    return v___x_4591_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11___boxed(
    mut v_00_u03b2_4592_: *mut LeanObject,
    mut v_keys_4593_: *mut LeanObject,
    mut v_vals_4594_: *mut LeanObject,
    mut v_heq_4595_: *mut LeanObject,
    mut v_i_4596_: *mut LeanObject,
    mut v_k_4597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4598_: *mut LeanObject = core::ptr::null_mut();
    v_res_4598_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__7_spec__8_spec__11(v_00_u03b2_4592_, v_keys_4593_, v_vals_4594_, v_heq_4595_, v_i_4596_, v_k_4597_);
    lean_dec_ref(v_k_4597_);
    lean_dec_ref(v_vals_4594_);
    lean_dec_ref(v_keys_4593_);
    return v_res_4598_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(
    mut v_00_u03b2_4599_: *mut LeanObject,
    mut v_x_4600_: *mut LeanObject,
    mut v_x_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    v___x_4602_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___redArg(v_x_4600_, v_x_4601_);
    return v___x_4602_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15___boxed(
    mut v_00_u03b2_4603_: *mut LeanObject,
    mut v_x_4604_: *mut LeanObject,
    mut v_x_4605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4606_: *mut LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15(v_00_u03b2_4603_, v_x_4604_, v_x_4605_);
    lean_dec_ref(v_x_4605_);
    lean_dec_ref(v_x_4604_);
    return v_res_4606_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16(
    mut v_00_u03b2_4607_: *mut LeanObject,
    mut v_x_4608_: *mut LeanObject,
    mut v_x_4609_: *mut LeanObject,
    mut v_x_4610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    v___x_4611_ = l_Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16___redArg(v_x_4608_, v_x_4609_, v_x_4610_);
    return v___x_4611_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(
    mut v_00_u03b2_4612_: *mut LeanObject,
    mut v_m_4613_: *mut LeanObject,
    mut v_a_4614_: *mut LeanObject,
) -> u8 {
    let mut v___x_4615_: u8 = 0;
    v___x_4615_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___redArg(v_m_4613_, v_a_4614_);
    return v___x_4615_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17___boxed(
    mut v_00_u03b2_4616_: *mut LeanObject,
    mut v_m_4617_: *mut LeanObject,
    mut v_a_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4619_: u8 = 0;
    let mut v_r_4620_: *mut LeanObject = core::ptr::null_mut();
    v_res_4619_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17(v_00_u03b2_4616_, v_m_4617_, v_a_4618_);
    lean_dec(v_a_4618_);
    lean_dec_ref(v_m_4617_);
    v_r_4620_ = lean_box((v_res_4619_) as usize);
    return v_r_4620_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12(
    mut v_00_u03b2_4621_: *mut LeanObject,
    mut v_x_4622_: *mut LeanObject,
    mut v_x_4623_: *mut LeanObject,
    mut v_x_4624_: *mut LeanObject,
    mut v_x_4625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    v___x_4626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__6_spec__6_spec__7_spec__12___redArg(v_x_4622_, v_x_4623_, v_x_4624_, v_x_4625_);
    return v___x_4626_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(
    mut v_00_u03b2_4627_: *mut LeanObject,
    mut v_x_4628_: *mut LeanObject,
    mut v_x_4629_: usize,
    mut v_x_4630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    v___x_4631_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___redArg(v_x_4628_, v_x_4629_, v_x_4630_);
    return v___x_4631_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18___boxed(
    mut v_00_u03b2_4632_: *mut LeanObject,
    mut v_x_4633_: *mut LeanObject,
    mut v_x_4634_: *mut LeanObject,
    mut v_x_4635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14748__boxed_4636_: usize = 0;
    let mut v_res_4637_: *mut LeanObject = core::ptr::null_mut();
    v_x_14748__boxed_4636_ = lean_unbox_usize(v_x_4634_);
    lean_dec(v_x_4634_);
    v_res_4637_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18(v_00_u03b2_4632_, v_x_4633_, v_x_14748__boxed_4636_, v_x_4635_);
    lean_dec_ref(v_x_4635_);
    lean_dec_ref(v_x_4633_);
    return v_res_4637_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(
    mut v_00_u03b2_4638_: *mut LeanObject,
    mut v_x_4639_: *mut LeanObject,
    mut v_x_4640_: usize,
    mut v_x_4641_: usize,
    mut v_x_4642_: *mut LeanObject,
    mut v_x_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___redArg(v_x_4639_, v_x_4640_, v_x_4641_, v_x_4642_, v_x_4643_);
    return v___x_4644_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20___boxed(
    mut v_00_u03b2_4645_: *mut LeanObject,
    mut v_x_4646_: *mut LeanObject,
    mut v_x_4647_: *mut LeanObject,
    mut v_x_4648_: *mut LeanObject,
    mut v_x_4649_: *mut LeanObject,
    mut v_x_4650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14759__boxed_4651_: usize = 0;
    let mut v_x_14760__boxed_4652_: usize = 0;
    let mut v_res_4653_: *mut LeanObject = core::ptr::null_mut();
    v_x_14759__boxed_4651_ = lean_unbox_usize(v_x_4647_);
    lean_dec(v_x_4647_);
    v_x_14760__boxed_4652_ = lean_unbox_usize(v_x_4648_);
    lean_dec(v_x_4648_);
    v_res_4653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20(v_00_u03b2_4645_, v_x_4646_, v_x_14759__boxed_4651_, v_x_14760__boxed_4652_, v_x_4649_, v_x_4650_);
    return v_res_4653_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(
    mut v_00_u03b2_4654_: *mut LeanObject,
    mut v_a_4655_: *mut LeanObject,
    mut v_x_4656_: *mut LeanObject,
) -> u8 {
    let mut v___x_4657_: u8 = 0;
    v___x_4657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___redArg(v_a_4655_, v_x_4656_);
    return v___x_4657_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22___boxed(
    mut v_00_u03b2_4658_: *mut LeanObject,
    mut v_a_4659_: *mut LeanObject,
    mut v_x_4660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4661_: u8 = 0;
    let mut v_r_4662_: *mut LeanObject = core::ptr::null_mut();
    v_res_4661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__17_spec__22(v_00_u03b2_4658_, v_a_4659_, v_x_4660_);
    lean_dec(v_x_4660_);
    lean_dec(v_a_4659_);
    v_r_4662_ = lean_box((v_res_4661_) as usize);
    return v_r_4662_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(
    mut v_00_u03b2_4663_: *mut LeanObject,
    mut v_keys_4664_: *mut LeanObject,
    mut v_vals_4665_: *mut LeanObject,
    mut v_heq_4666_: *mut LeanObject,
    mut v_i_4667_: *mut LeanObject,
    mut v_k_4668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    v___x_4669_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___redArg(v_keys_4664_, v_vals_4665_, v_i_4667_, v_k_4668_);
    return v___x_4669_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19___boxed(
    mut v_00_u03b2_4670_: *mut LeanObject,
    mut v_keys_4671_: *mut LeanObject,
    mut v_vals_4672_: *mut LeanObject,
    mut v_heq_4673_: *mut LeanObject,
    mut v_i_4674_: *mut LeanObject,
    mut v_k_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4676_: *mut LeanObject = core::ptr::null_mut();
    v_res_4676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__15_spec__18_spec__19(v_00_u03b2_4670_, v_keys_4671_, v_vals_4672_, v_heq_4673_, v_i_4674_, v_k_4675_);
    lean_dec_ref(v_k_4675_);
    lean_dec_ref(v_vals_4672_);
    lean_dec_ref(v_keys_4671_);
    return v_res_4676_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22(
    mut v_00_u03b2_4677_: *mut LeanObject,
    mut v_n_4678_: *mut LeanObject,
    mut v_k_4679_: *mut LeanObject,
    mut v_v_4680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    v___x_4681_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22___redArg(v_n_4678_, v_k_4679_, v_v_4680_);
    return v___x_4681_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(
    mut v_00_u03b2_4682_: *mut LeanObject,
    mut v_depth_4683_: usize,
    mut v_keys_4684_: *mut LeanObject,
    mut v_vals_4685_: *mut LeanObject,
    mut v_heq_4686_: *mut LeanObject,
    mut v_i_4687_: *mut LeanObject,
    mut v_entries_4688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    v___x_4689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___redArg(v_depth_4683_, v_keys_4684_, v_vals_4685_, v_i_4687_, v_entries_4688_);
    return v___x_4689_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23___boxed(
    mut v_00_u03b2_4690_: *mut LeanObject,
    mut v_depth_4691_: *mut LeanObject,
    mut v_keys_4692_: *mut LeanObject,
    mut v_vals_4693_: *mut LeanObject,
    mut v_heq_4694_: *mut LeanObject,
    mut v_i_4695_: *mut LeanObject,
    mut v_entries_4696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4697_: usize = 0;
    let mut v_res_4698_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4697_ = lean_unbox_usize(v_depth_4691_);
    lean_dec(v_depth_4691_);
    v_res_4698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__23(v_00_u03b2_4690_, v_depth_boxed_4697_, v_keys_4692_, v_vals_4693_, v_heq_4694_, v_i_4695_, v_entries_4696_);
    lean_dec_ref(v_vals_4693_);
    lean_dec_ref(v_keys_4692_);
    return v_res_4698_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24(
    mut v_00_u03b2_4699_: *mut LeanObject,
    mut v_x_4700_: *mut LeanObject,
    mut v_x_4701_: *mut LeanObject,
    mut v_x_4702_: *mut LeanObject,
    mut v_x_4703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    v___x_4704_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Environment_realizeValue___at___00Lean_Meta_realizeValue___at___00__private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__9_spec__11_spec__16_spec__20_spec__22_spec__24___redArg(v_x_4700_, v_x_4701_, v_x_4702_, v_x_4703_);
    return v___x_4704_;
}
pub unsafe fn l_Lean_Meta_getFunInfo(
    mut v_fn_4705_: *mut LeanObject,
    mut v_maxArgs_x3f_4706_: *mut LeanObject,
    mut v_a_4707_: *mut LeanObject,
    mut v_a_4708_: *mut LeanObject,
    mut v_a_4709_: *mut LeanObject,
    mut v_a_4710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    v___x_4712_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(
        v_fn_4705_,
        v_maxArgs_x3f_4706_,
        v_a_4707_,
        v_a_4708_,
        v_a_4709_,
        v_a_4710_,
    );
    return v___x_4712_;
}
pub unsafe fn l_Lean_Meta_getFunInfo___boxed(
    mut v_fn_4713_: *mut LeanObject,
    mut v_maxArgs_x3f_4714_: *mut LeanObject,
    mut v_a_4715_: *mut LeanObject,
    mut v_a_4716_: *mut LeanObject,
    mut v_a_4717_: *mut LeanObject,
    mut v_a_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4720_: *mut LeanObject = core::ptr::null_mut();
    v_res_4720_ = l_Lean_Meta_getFunInfo(
        v_fn_4713_,
        v_maxArgs_x3f_4714_,
        v_a_4715_,
        v_a_4716_,
        v_a_4717_,
        v_a_4718_,
    );
    lean_dec(v_a_4718_);
    lean_dec_ref(v_a_4717_);
    lean_dec(v_a_4716_);
    lean_dec_ref(v_a_4715_);
    return v_res_4720_;
}
pub unsafe fn l_Lean_Meta_getFunInfoNArgs(
    mut v_fn_4721_: *mut LeanObject,
    mut v_nargs_4722_: *mut LeanObject,
    mut v_a_4723_: *mut LeanObject,
    mut v_a_4724_: *mut LeanObject,
    mut v_a_4725_: *mut LeanObject,
    mut v_a_4726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    v___x_4728_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4728_, 0, v_nargs_4722_);
    v___x_4729_ = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(
        v_fn_4721_,
        v___x_4728_,
        v_a_4723_,
        v_a_4724_,
        v_a_4725_,
        v_a_4726_,
    );
    return v___x_4729_;
}
pub unsafe fn l_Lean_Meta_getFunInfoNArgs___boxed(
    mut v_fn_4730_: *mut LeanObject,
    mut v_nargs_4731_: *mut LeanObject,
    mut v_a_4732_: *mut LeanObject,
    mut v_a_4733_: *mut LeanObject,
    mut v_a_4734_: *mut LeanObject,
    mut v_a_4735_: *mut LeanObject,
    mut v_a_4736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4737_: *mut LeanObject = core::ptr::null_mut();
    v_res_4737_ = l_Lean_Meta_getFunInfoNArgs(
        v_fn_4730_,
        v_nargs_4731_,
        v_a_4732_,
        v_a_4733_,
        v_a_4734_,
        v_a_4735_,
    );
    lean_dec(v_a_4735_);
    lean_dec_ref(v_a_4734_);
    lean_dec(v_a_4733_);
    lean_dec_ref(v_a_4732_);
    return v_res_4737_;
}
pub unsafe fn l_Lean_Meta_FunInfo_getArity(mut v_info_4738_: *mut LeanObject) -> *mut LeanObject {
    let mut v_paramInfo_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    v_paramInfo_4739_ = lean_ctor_get(v_info_4738_, 0);
    v___x_4740_ = lean_array_get_size(v_paramInfo_4739_);
    return v___x_4740_;
}
pub unsafe fn l_Lean_Meta_FunInfo_getArity___boxed(
    mut v_info_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4742_: *mut LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_Lean_Meta_FunInfo_getArity(v_info_4741_);
    lean_dec_ref(v_info_4741_);
    return v_res_4742_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_FunInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_FunInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_FunInfo(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_FunInfo(builtin);
}

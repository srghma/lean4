// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Util
// Imports: Lean.Meta.Tactic.Grind.AC.Types Lean.Meta.Tactic.Grind.ProveEq Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Simp
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isApp, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Types::{
    initialize_Lean_Meta_Tactic_Grind_AC_Types, l_Lean_Meta_Grind_AC_acExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
    l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::ProveEq::{
    initialize_Lean_Meta_Tactic_Grind_ProveEq, runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_preprocessLight___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_getState___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_getConfig___redArg,
    l_Lean_Meta_Grind_getGeneration___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
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
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_internalize;
use crate::lean_imports_rs::Lean::MetavarContext::lean_instantiate_expr_mvars;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_12, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value: LeanStringObject<45> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101,
            114, 114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 115, 116, 114, 117,
            99, 116, 117, 114, 101, 32, 105, 100, 0,
        ],
    };
static mut l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_instMonadGetStructACM_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_AC_ACM_getStruct___boxed as *const core::ffi::c_void,
        m_arity: 12,
        m_num_fixed: 0,
        m_objs: [],
    };
pub static mut l_Lean_Meta_Grind_AC_instMonadGetStructACM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instMonadGetStructACM_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value) as *mut LeanObject,9743492140944907313 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value) as *mut LeanObject,14181099489592536354 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value) as *mut LeanObject,9917798623386220051 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [71, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [103, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value
) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value) as *mut LeanObject,854136310249810287 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value) as *mut LeanObject,8801718159307809986 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value) as *mut LeanObject,18356704233129443855 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value) as *mut LeanObject,8391571994004792969 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value) as *mut LeanObject,105488867511536770 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value) as *mut LeanObject,17878876274162330439 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value) as *mut LeanObject,11833570877100518198 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value) as *mut LeanObject,8347582161988589016 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value) as *mut LeanObject,7316284823769321069 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value) as *mut LeanObject,1611444129324655608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value) as *mut LeanObject,16856108565602861689 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value) as *mut LeanObject,4187025665268973031 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value) as *mut LeanObject,11858238400308895562 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value) as *mut LeanObject,6100819061652633370 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value) as *mut LeanObject,12847922472053947547 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value) as *mut LeanObject,10422657989269798688 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [44, 32, 110, 101, 117, 116, 114, 97, 108, 63, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [60, 110, 111, 116, 45, 97, 118, 97, 105, 108, 97, 98, 108, 101, 62, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [44, 32, 105, 100, 101, 109, 112, 111, 116, 101, 110, 116, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value) as *mut LeanObject,13988555943647875614 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value) as *mut LeanObject,15368431810600006387 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 32, 99, 111, 109, 109, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [65, 115, 115, 111, 99, 105, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value) as *mut LeanObject,17561379004628073218 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 109, 109, 117, 116, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value) as *mut LeanObject,234445833000607850 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [73, 100, 101, 109, 112, 111, 116, 101, 110, 116, 79, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value) as *mut LeanObject,16442335306435255285 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 97, 119, 102, 117, 108, 73, 100, 101, 110, 116, 105, 116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value) as *mut LeanObject,18153903751919310386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27___redArg(
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2491_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2492_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_2491_, v_a_2488_, v_a_2489_);
    return v___x_2492_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27___redArg___boxed(
    mut v_a_2493_: *mut LeanObject,
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2496_: *mut LeanObject = core::ptr::null_mut();
    v_res_2496_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2493_, v_a_2494_);
    lean_dec_ref(v_a_2494_);
    lean_dec(v_a_2493_);
    return v_res_2496_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27(
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
    mut v_a_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2497_, v_a_2505_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27___boxed(
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
    mut v_a_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
    mut v_a_2517_: *mut LeanObject,
    mut v_a_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2520_: *mut LeanObject = core::ptr::null_mut();
    v_res_2520_ = l_Lean_Meta_Grind_AC_get_x27(
        v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_,
        v_a_2517_, v_a_2518_,
    );
    lean_dec(v_a_2518_);
    lean_dec_ref(v_a_2517_);
    lean_dec(v_a_2516_);
    lean_dec_ref(v_a_2515_);
    lean_dec(v_a_2514_);
    lean_dec_ref(v_a_2513_);
    lean_dec(v_a_2512_);
    lean_dec_ref(v_a_2511_);
    lean_dec(v_a_2510_);
    lean_dec(v_a_2509_);
    return v_res_2520_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27___redArg(
    mut v_f_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2525_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2524_, v_f_2521_, v_a_2522_);
    return v___x_2525_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27___redArg___boxed(
    mut v_f_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Lean_Meta_Grind_AC_modify_x27___redArg(v_f_2526_, v_a_2527_);
    lean_dec(v_a_2527_);
    return v_res_2529_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27(
    mut v_f_2530_: *mut LeanObject,
    mut v_a_2531_: *mut LeanObject,
    mut v_a_2532_: *mut LeanObject,
    mut v_a_2533_: *mut LeanObject,
    mut v_a_2534_: *mut LeanObject,
    mut v_a_2535_: *mut LeanObject,
    mut v_a_2536_: *mut LeanObject,
    mut v_a_2537_: *mut LeanObject,
    mut v_a_2538_: *mut LeanObject,
    mut v_a_2539_: *mut LeanObject,
    mut v_a_2540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    v___x_2542_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2543_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2542_, v_f_2530_, v_a_2531_);
    return v___x_2543_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27___boxed(
    mut v_f_2544_: *mut LeanObject,
    mut v_a_2545_: *mut LeanObject,
    mut v_a_2546_: *mut LeanObject,
    mut v_a_2547_: *mut LeanObject,
    mut v_a_2548_: *mut LeanObject,
    mut v_a_2549_: *mut LeanObject,
    mut v_a_2550_: *mut LeanObject,
    mut v_a_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
    mut v_a_2553_: *mut LeanObject,
    mut v_a_2554_: *mut LeanObject,
    mut v_a_2555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2556_: *mut LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Lean_Meta_Grind_AC_modify_x27(
        v_f_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_,
        v_a_2552_, v_a_2553_, v_a_2554_,
    );
    lean_dec(v_a_2554_);
    lean_dec_ref(v_a_2553_);
    lean_dec(v_a_2552_);
    lean_dec_ref(v_a_2551_);
    lean_dec(v_a_2550_);
    lean_dec_ref(v_a_2549_);
    lean_dec(v_a_2548_);
    lean_dec_ref(v_a_2547_);
    lean_dec(v_a_2546_);
    lean_dec(v_a_2545_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(
    mut v_a_2557_: *mut LeanObject,
    mut v_a_2558_: *mut LeanObject,
    mut v_a_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v_acSteps_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v_a_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut v_a_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2587_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2561_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2557_, v_a_2559_);
                if lean_obj_tag(v___x_2561_) == 0 {
                    v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
                    lean_inc(v_a_2562_);
                    lean_dec_ref_known(v___x_2561_, 1);
                    v___x_2563_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2558_);
                    if lean_obj_tag(v___x_2563_) == 0 {
                        v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
                        v_isSharedCheck_2575_ = (!lean_is_exclusive(v___x_2563_)) as u8;
                        if v_isSharedCheck_2575_ == 0 {
                            v___x_2566_ = v___x_2563_;
                            v_isShared_2567_ = v_isSharedCheck_2575_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2564_);
                            lean_dec(v___x_2563_);
                            v___x_2566_ = lean_box(0);
                            v_isShared_2567_ = v_isSharedCheck_2575_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2562_);
                        v_a_2576_ = lean_ctor_get(v___x_2563_, 0);
                        v_isSharedCheck_2583_ = (!lean_is_exclusive(v___x_2563_)) as u8;
                        if v_isSharedCheck_2583_ == 0 {
                            v___x_2578_ = v___x_2563_;
                            v_isShared_2579_ = v_isSharedCheck_2583_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2576_);
                            lean_dec(v___x_2563_);
                            v___x_2578_ = lean_box(0);
                            v_isShared_2579_ = v_isSharedCheck_2583_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2584_ = lean_ctor_get(v___x_2561_, 0);
                    v_isSharedCheck_2591_ = (!lean_is_exclusive(v___x_2561_)) as u8;
                    if v_isSharedCheck_2591_ == 0 {
                        v___x_2586_ = v___x_2561_;
                        v_isShared_2587_ = v_isSharedCheck_2591_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2584_);
                        lean_dec(v___x_2561_);
                        v___x_2586_ = lean_box(0);
                        v_isShared_2587_ = v_isSharedCheck_2591_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_acSteps_2568_ = lean_ctor_get(v_a_2564_, 8);
                lean_inc(v_acSteps_2568_);
                lean_dec(v_a_2564_);
                v_steps_2569_ = lean_ctor_get(v_a_2562_, 3);
                lean_inc(v_steps_2569_);
                lean_dec(v_a_2562_);
                v___x_2570_ = lean_nat_dec_le(v_acSteps_2568_, v_steps_2569_);
                lean_dec(v_steps_2569_);
                lean_dec(v_acSteps_2568_);
                v___x_2571_ = lean_box((v___x_2570_) as usize);
                if v_isShared_2567_ == 0 {
                    lean_ctor_set(v___x_2566_, 0, v___x_2571_);
                    v___x_2573_ = v___x_2566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
                    v___x_2573_ = v_reuseFailAlloc_2574_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2573_;
            }
            3 => {
                if v_isShared_2579_ == 0 {
                    v___x_2581_ = v___x_2578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
                    v___x_2581_ = v_reuseFailAlloc_2582_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2581_;
            }
            5 => {
                if v_isShared_2587_ == 0 {
                    v___x_2589_ = v___x_2586_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps___redArg___boxed(
    mut v_a_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2596_: *mut LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_2592_, v_a_2593_, v_a_2594_);
    lean_dec_ref(v_a_2594_);
    lean_dec_ref(v_a_2593_);
    lean_dec(v_a_2592_);
    return v_res_2596_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps(
    mut v_a_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
    mut v_a_2602_: *mut LeanObject,
    mut v_a_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    v___x_2608_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_2597_, v_a_2599_, v_a_2605_);
    return v___x_2608_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps___boxed(
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
    mut v_a_2615_: *mut LeanObject,
    mut v_a_2616_: *mut LeanObject,
    mut v_a_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2620_: *mut LeanObject = core::ptr::null_mut();
    v_res_2620_ = l_Lean_Meta_Grind_AC_checkMaxSteps(
        v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_,
        v_a_2617_, v_a_2618_,
    );
    lean_dec(v_a_2618_);
    lean_dec_ref(v_a_2617_);
    lean_dec(v_a_2616_);
    lean_dec_ref(v_a_2615_);
    lean_dec(v_a_2614_);
    lean_dec_ref(v_a_2613_);
    lean_dec(v_a_2612_);
    lean_dec_ref(v_a_2611_);
    lean_dec(v_a_2610_);
    lean_dec(v_a_2609_);
    return v_res_2620_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0(
    mut v_s_2621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2622_ = lean_ctor_get(v_s_2621_, 0);
                v_opIdOf_2623_ = lean_ctor_get(v_s_2621_, 1);
                v_exprToOpIds_2624_ = lean_ctor_get(v_s_2621_, 2);
                v_steps_2625_ = lean_ctor_get(v_s_2621_, 3);
                v_isSharedCheck_2634_ = (!lean_is_exclusive(v_s_2621_)) as u8;
                if v_isSharedCheck_2634_ == 0 {
                    v___x_2627_ = v_s_2621_;
                    v_isShared_2628_ = v_isSharedCheck_2634_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_2625_);
                    lean_inc(v_exprToOpIds_2624_);
                    lean_inc(v_opIdOf_2623_);
                    lean_inc(v_structs_2622_);
                    lean_dec(v_s_2621_);
                    v___x_2627_ = lean_box(0);
                    v_isShared_2628_ = v_isSharedCheck_2634_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2629_ = lean_unsigned_to_nat(1);
                v___x_2630_ = lean_nat_add(v_steps_2625_, v___x_2629_);
                lean_dec(v_steps_2625_);
                if v_isShared_2628_ == 0 {
                    lean_ctor_set(v___x_2627_, 3, v___x_2630_);
                    v___x_2632_ = v___x_2627_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_structs_2622_);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_opIdOf_2623_);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 2, v_exprToOpIds_2624_);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 3, v___x_2630_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___redArg(
    mut v_a_2636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    v___f_2638_ = l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0;
    v___x_2639_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2640_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2639_, v___f_2638_, v_a_2636_);
    return v___x_2640_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___redArg___boxed(
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2643_: *mut LeanObject = core::ptr::null_mut();
    v_res_2643_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_2641_);
    lean_dec(v_a_2641_);
    return v_res_2643_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps(
    mut v_a_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
    mut v_a_2653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    v___x_2655_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_2644_);
    return v___x_2655_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___boxed(
    mut v_a_2656_: *mut LeanObject,
    mut v_a_2657_: *mut LeanObject,
    mut v_a_2658_: *mut LeanObject,
    mut v_a_2659_: *mut LeanObject,
    mut v_a_2660_: *mut LeanObject,
    mut v_a_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
    mut v_a_2663_: *mut LeanObject,
    mut v_a_2664_: *mut LeanObject,
    mut v_a_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2667_: *mut LeanObject = core::ptr::null_mut();
    v_res_2667_ = l_Lean_Meta_Grind_AC_incSteps(
        v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_,
        v_a_2664_, v_a_2665_,
    );
    lean_dec(v_a_2665_);
    lean_dec_ref(v_a_2664_);
    lean_dec(v_a_2663_);
    lean_dec_ref(v_a_2662_);
    lean_dec(v_a_2661_);
    lean_dec_ref(v_a_2660_);
    lean_dec(v_a_2659_);
    lean_dec_ref(v_a_2658_);
    lean_dec(v_a_2657_);
    lean_dec(v_a_2656_);
    return v_res_2667_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift___redArg(
    mut v_inst_2668_: *mut LeanObject,
    mut v_inst_2669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    v___x_2670_ = lean_apply_2(v_inst_2668_, lean_box(0), v_inst_2669_);
    return v___x_2670_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift(
    mut v_m_2671_: *mut LeanObject,
    mut v_n_2672_: *mut LeanObject,
    mut v_inst_2673_: *mut LeanObject,
    mut v_inst_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    v___x_2675_ = lean_apply_2(v_inst_2673_, lean_box(0), v_inst_2674_);
    return v___x_2675_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run___redArg(
    mut v_opId_2676_: *mut LeanObject,
    mut v_x_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
    mut v_a_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
    mut v_a_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2687_);
    lean_inc_ref(v_a_2686_);
    lean_inc(v_a_2685_);
    lean_inc_ref(v_a_2684_);
    lean_inc(v_a_2683_);
    lean_inc_ref(v_a_2682_);
    lean_inc(v_a_2681_);
    lean_inc_ref(v_a_2680_);
    lean_inc(v_a_2679_);
    lean_inc(v_a_2678_);
    v___x_2689_ = lean_apply_12(
        v_x_2677_,
        v_opId_2676_,
        v_a_2678_,
        v_a_2679_,
        v_a_2680_,
        v_a_2681_,
        v_a_2682_,
        v_a_2683_,
        v_a_2684_,
        v_a_2685_,
        v_a_2686_,
        v_a_2687_,
        lean_box(0),
    );
    return v___x_2689_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run___redArg___boxed(
    mut v_opId_2690_: *mut LeanObject,
    mut v_x_2691_: *mut LeanObject,
    mut v_a_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
    mut v_a_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
    mut v_a_2700_: *mut LeanObject,
    mut v_a_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2703_: *mut LeanObject = core::ptr::null_mut();
    v_res_2703_ = l_Lean_Meta_Grind_AC_ACM_run___redArg(
        v_opId_2690_,
        v_x_2691_,
        v_a_2692_,
        v_a_2693_,
        v_a_2694_,
        v_a_2695_,
        v_a_2696_,
        v_a_2697_,
        v_a_2698_,
        v_a_2699_,
        v_a_2700_,
        v_a_2701_,
    );
    lean_dec(v_a_2701_);
    lean_dec_ref(v_a_2700_);
    lean_dec(v_a_2699_);
    lean_dec_ref(v_a_2698_);
    lean_dec(v_a_2697_);
    lean_dec_ref(v_a_2696_);
    lean_dec(v_a_2695_);
    lean_dec_ref(v_a_2694_);
    lean_dec(v_a_2693_);
    lean_dec(v_a_2692_);
    return v_res_2703_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run(
    mut v_00_u03b1_2704_: *mut LeanObject,
    mut v_opId_2705_: *mut LeanObject,
    mut v_x_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
    mut v_a_2709_: *mut LeanObject,
    mut v_a_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2716_);
    lean_inc_ref(v_a_2715_);
    lean_inc(v_a_2714_);
    lean_inc_ref(v_a_2713_);
    lean_inc(v_a_2712_);
    lean_inc_ref(v_a_2711_);
    lean_inc(v_a_2710_);
    lean_inc_ref(v_a_2709_);
    lean_inc(v_a_2708_);
    lean_inc(v_a_2707_);
    v___x_2718_ = lean_apply_12(
        v_x_2706_,
        v_opId_2705_,
        v_a_2707_,
        v_a_2708_,
        v_a_2709_,
        v_a_2710_,
        v_a_2711_,
        v_a_2712_,
        v_a_2713_,
        v_a_2714_,
        v_a_2715_,
        v_a_2716_,
        lean_box(0),
    );
    return v___x_2718_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run___boxed(
    mut v_00_u03b1_2719_: *mut LeanObject,
    mut v_opId_2720_: *mut LeanObject,
    mut v_x_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v_a_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_a_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
    mut v_a_2732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2733_: *mut LeanObject = core::ptr::null_mut();
    v_res_2733_ = l_Lean_Meta_Grind_AC_ACM_run(
        v_00_u03b1_2719_,
        v_opId_2720_,
        v_x_2721_,
        v_a_2722_,
        v_a_2723_,
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
        v_a_2727_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        v_a_2731_,
    );
    lean_dec(v_a_2731_);
    lean_dec_ref(v_a_2730_);
    lean_dec(v_a_2729_);
    lean_dec_ref(v_a_2728_);
    lean_dec(v_a_2727_);
    lean_dec_ref(v_a_2726_);
    lean_dec(v_a_2725_);
    lean_dec_ref(v_a_2724_);
    lean_dec(v_a_2723_);
    lean_dec(v_a_2722_);
    return v_res_2733_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId___redArg(
    mut v_a_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2734_);
    v___x_2736_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2736_, 0, v_a_2734_);
    return v___x_2736_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId___redArg___boxed(
    mut v_a_2737_: *mut LeanObject,
    mut v_a_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2739_: *mut LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Lean_Meta_Grind_AC_getOpId___redArg(v_a_2737_);
    lean_dec(v_a_2737_);
    return v_res_2739_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId(
    mut v_a_2740_: *mut LeanObject,
    mut v_a_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
    mut v_a_2745_: *mut LeanObject,
    mut v_a_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_a_2748_: *mut LeanObject,
    mut v_a_2749_: *mut LeanObject,
    mut v_a_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2740_);
    v___x_2752_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2752_, 0, v_a_2740_);
    return v___x_2752_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId___boxed(
    mut v_a_2753_: *mut LeanObject,
    mut v_a_2754_: *mut LeanObject,
    mut v_a_2755_: *mut LeanObject,
    mut v_a_2756_: *mut LeanObject,
    mut v_a_2757_: *mut LeanObject,
    mut v_a_2758_: *mut LeanObject,
    mut v_a_2759_: *mut LeanObject,
    mut v_a_2760_: *mut LeanObject,
    mut v_a_2761_: *mut LeanObject,
    mut v_a_2762_: *mut LeanObject,
    mut v_a_2763_: *mut LeanObject,
    mut v_a_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2765_: *mut LeanObject = core::ptr::null_mut();
    v_res_2765_ = l_Lean_Meta_Grind_AC_getOpId(
        v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_,
        v_a_2761_, v_a_2762_, v_a_2763_,
    );
    lean_dec(v_a_2763_);
    lean_dec_ref(v_a_2762_);
    lean_dec(v_a_2761_);
    lean_dec_ref(v_a_2760_);
    lean_dec(v_a_2759_);
    lean_dec_ref(v_a_2758_);
    lean_dec(v_a_2757_);
    lean_dec_ref(v_a_2756_);
    lean_dec(v_a_2755_);
    lean_dec(v_a_2754_);
    lean_dec(v_a_2753_);
    return v_res_2765_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(
    mut v_msgData_2766_: *mut LeanObject,
    mut v___y_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    v___x_2772_ = lean_st_ref_get(v___y_2770_);
    v_env_2773_ = lean_ctor_get(v___x_2772_, 0);
    lean_inc_ref(v_env_2773_);
    lean_dec(v___x_2772_);
    v___x_2774_ = lean_st_ref_get(v___y_2768_);
    v_mctx_2775_ = lean_ctor_get(v___x_2774_, 0);
    lean_inc_ref(v_mctx_2775_);
    lean_dec(v___x_2774_);
    v_lctx_2776_ = lean_ctor_get(v___y_2767_, 2);
    v_options_2777_ = lean_ctor_get(v___y_2769_, 2);
    lean_inc_ref(v_options_2777_);
    lean_inc_ref(v_lctx_2776_);
    v___x_2778_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2778_, 0, v_env_2773_);
    lean_ctor_set(v___x_2778_, 1, v_mctx_2775_);
    lean_ctor_set(v___x_2778_, 2, v_lctx_2776_);
    lean_ctor_set(v___x_2778_, 3, v_options_2777_);
    v___x_2779_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2779_, 0, v___x_2778_);
    lean_ctor_set(v___x_2779_, 1, v_msgData_2766_);
    v___x_2780_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2780_, 0, v___x_2779_);
    return v___x_2780_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(
    mut v_msgData_2781_: *mut LeanObject,
    mut v___y_2782_: *mut LeanObject,
    mut v___y_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2787_: *mut LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msgData_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
    lean_dec(v___y_2785_);
    lean_dec_ref(v___y_2784_);
    lean_dec(v___y_2783_);
    lean_dec_ref(v___y_2782_);
    return v_res_2787_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(
    mut v_msg_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
    mut v___y_2791_: *mut LeanObject,
    mut v___y_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2794_ = lean_ctor_get(v___y_2791_, 5);
                v___x_2795_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
                v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
                v_isSharedCheck_2804_ = (!lean_is_exclusive(v___x_2795_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v___x_2798_ = v___x_2795_;
                    v_isShared_2799_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2796_);
                    lean_dec(v___x_2795_);
                    v___x_2798_ = lean_box(0);
                    v_isShared_2799_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2794_);
                v___x_2800_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2800_, 0, v_ref_2794_);
                lean_ctor_set(v___x_2800_, 1, v_a_2796_);
                if v_isShared_2799_ == 0 {
                    lean_ctor_set_tag(v___x_2798_, 1);
                    lean_ctor_set(v___x_2798_, 0, v___x_2800_);
                    v___x_2802_ = v___x_2798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
                    v___x_2802_ = v_reuseFailAlloc_2803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(
    mut v_msg_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
    mut v___y_2808_: *mut LeanObject,
    mut v___y_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2811_: *mut LeanObject = core::ptr::null_mut();
    v_res_2811_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(
        v_msg_2805_,
        v___y_2806_,
        v___y_2807_,
        v___y_2808_,
        v___y_2809_,
    );
    lean_dec(v___y_2809_);
    lean_dec_ref(v___y_2808_);
    lean_dec(v___y_2807_);
    lean_dec_ref(v___y_2806_);
    return v_res_2811_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1() -> *mut LeanObject {
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    v___x_2813_ = l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0;
    v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_getStruct(
    mut v_a_2815_: *mut LeanObject,
    mut v_a_2816_: *mut LeanObject,
    mut v_a_2817_: *mut LeanObject,
    mut v_a_2818_: *mut LeanObject,
    mut v_a_2819_: *mut LeanObject,
    mut v_a_2820_: *mut LeanObject,
    mut v_a_2821_: *mut LeanObject,
    mut v_a_2822_: *mut LeanObject,
    mut v_a_2823_: *mut LeanObject,
    mut v_a_2824_: *mut LeanObject,
    mut v_a_2825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v_structs_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_a_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2827_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2816_, v_a_2824_);
                if lean_obj_tag(v___x_2827_) == 0 {
                    v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
                    v_isSharedCheck_2841_ = (!lean_is_exclusive(v___x_2827_)) as u8;
                    if v_isSharedCheck_2841_ == 0 {
                        v___x_2830_ = v___x_2827_;
                        v_isShared_2831_ = v_isSharedCheck_2841_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2828_);
                        lean_dec(v___x_2827_);
                        v___x_2830_ = lean_box(0);
                        v_isShared_2831_ = v_isSharedCheck_2841_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2842_ = lean_ctor_get(v___x_2827_, 0);
                    v_isSharedCheck_2849_ = (!lean_is_exclusive(v___x_2827_)) as u8;
                    if v_isSharedCheck_2849_ == 0 {
                        v___x_2844_ = v___x_2827_;
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2842_);
                        lean_dec(v___x_2827_);
                        v___x_2844_ = lean_box(0);
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_structs_2832_ = lean_ctor_get(v_a_2828_, 0);
                lean_inc_ref(v_structs_2832_);
                lean_dec(v_a_2828_);
                v___x_2833_ = lean_array_get_size(v_structs_2832_);
                v___x_2834_ = lean_nat_dec_lt(v_a_2815_, v___x_2833_);
                if v___x_2834_ == 0 {
                    lean_dec_ref(v_structs_2832_);
                    lean_del_object(v___x_2830_);
                    v___x_2835_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1,
                    );
                    v___x_2836_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v___x_2835_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
                    return v___x_2836_;
                } else {
                    v___x_2837_ = lean_array_fget(v_structs_2832_, v_a_2815_);
                    lean_dec_ref(v_structs_2832_);
                    if v_isShared_2831_ == 0 {
                        lean_ctor_set(v___x_2830_, 0, v___x_2837_);
                        v___x_2839_ = v___x_2830_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
                        v___x_2839_ = v_reuseFailAlloc_2840_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2839_;
            }
            3 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(
    mut v_a_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
    mut v_a_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
    mut v_a_2855_: *mut LeanObject,
    mut v_a_2856_: *mut LeanObject,
    mut v_a_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
    mut v_a_2861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2862_: *mut LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
        v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_,
        v_a_2858_, v_a_2859_, v_a_2860_,
    );
    lean_dec(v_a_2860_);
    lean_dec_ref(v_a_2859_);
    lean_dec(v_a_2858_);
    lean_dec_ref(v_a_2857_);
    lean_dec(v_a_2856_);
    lean_dec_ref(v_a_2855_);
    lean_dec(v_a_2854_);
    lean_dec_ref(v_a_2853_);
    lean_dec(v_a_2852_);
    lean_dec(v_a_2851_);
    lean_dec(v_a_2850_);
    return v_res_2862_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(
    mut v_00_u03b1_2863_: *mut LeanObject,
    mut v_msg_2864_: *mut LeanObject,
    mut v___y_2865_: *mut LeanObject,
    mut v___y_2866_: *mut LeanObject,
    mut v___y_2867_: *mut LeanObject,
    mut v___y_2868_: *mut LeanObject,
    mut v___y_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    v___x_2877_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(
        v_msg_2864_,
        v___y_2872_,
        v___y_2873_,
        v___y_2874_,
        v___y_2875_,
    );
    return v___x_2877_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(
    mut v_00_u03b1_2878_: *mut LeanObject,
    mut v_msg_2879_: *mut LeanObject,
    mut v___y_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
    mut v___y_2882_: *mut LeanObject,
    mut v___y_2883_: *mut LeanObject,
    mut v___y_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
    mut v___y_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
    mut v___y_2888_: *mut LeanObject,
    mut v___y_2889_: *mut LeanObject,
    mut v___y_2890_: *mut LeanObject,
    mut v___y_2891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2892_: *mut LeanObject = core::ptr::null_mut();
    v_res_2892_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(
        v_00_u03b1_2878_,
        v_msg_2879_,
        v___y_2880_,
        v___y_2881_,
        v___y_2882_,
        v___y_2883_,
        v___y_2884_,
        v___y_2885_,
        v___y_2886_,
        v___y_2887_,
        v___y_2888_,
        v___y_2889_,
        v___y_2890_,
    );
    lean_dec(v___y_2890_);
    lean_dec_ref(v___y_2889_);
    lean_dec(v___y_2888_);
    lean_dec_ref(v___y_2887_);
    lean_dec(v___y_2886_);
    lean_dec_ref(v___y_2885_);
    lean_dec(v___y_2884_);
    lean_dec_ref(v___y_2883_);
    lean_dec(v___y_2882_);
    lean_dec(v___y_2881_);
    lean_dec(v___y_2880_);
    return v_res_2892_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(
    mut v_a_2894_: *mut LeanObject,
    mut v_f_2895_: *mut LeanObject,
    mut v_s_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v_v_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v_unused_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2897_ = lean_ctor_get(v_s_2896_, 0);
                v_opIdOf_2898_ = lean_ctor_get(v_s_2896_, 1);
                v_exprToOpIds_2899_ = lean_ctor_get(v_s_2896_, 2);
                v_steps_2900_ = lean_ctor_get(v_s_2896_, 3);
                v___x_2901_ = lean_array_get_size(v_structs_2897_);
                v___x_2902_ = lean_nat_dec_lt(v_a_2894_, v___x_2901_);
                if v___x_2902_ == 0 {
                    lean_dec_ref(v_f_2895_);
                    return v_s_2896_;
                } else {
                    lean_inc(v_steps_2900_);
                    lean_inc_ref(v_exprToOpIds_2899_);
                    lean_inc_ref(v_opIdOf_2898_);
                    lean_inc_ref(v_structs_2897_);
                    v_isSharedCheck_2914_ = (!lean_is_exclusive(v_s_2896_)) as u8;
                    if v_isSharedCheck_2914_ == 0 {
                        v_unused_2915_ = lean_ctor_get(v_s_2896_, 3);
                        lean_dec(v_unused_2915_);
                        v_unused_2916_ = lean_ctor_get(v_s_2896_, 2);
                        lean_dec(v_unused_2916_);
                        v_unused_2917_ = lean_ctor_get(v_s_2896_, 1);
                        lean_dec(v_unused_2917_);
                        v_unused_2918_ = lean_ctor_get(v_s_2896_, 0);
                        lean_dec(v_unused_2918_);
                        v___x_2904_ = v_s_2896_;
                        v_isShared_2905_ = v_isSharedCheck_2914_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_2896_);
                        v___x_2904_ = lean_box(0);
                        v_isShared_2905_ = v_isSharedCheck_2914_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2906_ = lean_array_fget(v_structs_2897_, v_a_2894_);
                v___x_2907_ = lean_box(0);
                v_xs_x27_2908_ = lean_array_fset(v_structs_2897_, v_a_2894_, v___x_2907_);
                v___x_2909_ = lean_apply_1(v_f_2895_, v_v_2906_);
                v___x_2910_ = lean_array_fset(v_xs_x27_2908_, v_a_2894_, v___x_2909_);
                if v_isShared_2905_ == 0 {
                    lean_ctor_set(v___x_2904_, 0, v___x_2910_);
                    v___x_2912_ = v___x_2904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_opIdOf_2898_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_exprToOpIds_2899_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_steps_2900_);
                    v___x_2912_ = v_reuseFailAlloc_2913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(
    mut v_a_2919_: *mut LeanObject,
    mut v_f_2920_: *mut LeanObject,
    mut v_s_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2922_: *mut LeanObject = core::ptr::null_mut();
    v_res_2922_ =
        l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(v_a_2919_, v_f_2920_, v_s_2921_);
    lean_dec(v_a_2919_);
    return v_res_2922_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg(
    mut v_f_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2924_);
    v___f_2927_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2927_, 0, v_a_2924_);
    lean_closure_set(v___f_2927_, 1, v_f_2923_);
    v___x_2928_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2929_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2928_, v___f_2927_, v_a_2925_);
    return v___x_2929_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(
    mut v_f_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2934_: *mut LeanObject = core::ptr::null_mut();
    v_res_2934_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_2930_, v_a_2931_, v_a_2932_);
    lean_dec(v_a_2932_);
    lean_dec(v_a_2931_);
    return v_res_2934_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct(
    mut v_f_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___x_2948_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_2935_, v_a_2936_, v_a_2937_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___boxed(
    mut v_f_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
    mut v_a_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
    mut v_a_2953_: *mut LeanObject,
    mut v_a_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
    mut v_a_2958_: *mut LeanObject,
    mut v_a_2959_: *mut LeanObject,
    mut v_a_2960_: *mut LeanObject,
    mut v_a_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2962_: *mut LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Meta_Grind_AC_modifyStruct(
        v_f_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_,
        v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_,
    );
    lean_dec(v_a_2960_);
    lean_dec_ref(v_a_2959_);
    lean_dec(v_a_2958_);
    lean_dec_ref(v_a_2957_);
    lean_dec(v_a_2956_);
    lean_dec_ref(v_a_2955_);
    lean_dec(v_a_2954_);
    lean_dec_ref(v_a_2953_);
    lean_dec(v_a_2952_);
    lean_dec(v_a_2951_);
    lean_dec(v_a_2950_);
    return v_res_2962_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOp(
    mut v_a_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
    mut v_a_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v_op_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v_a_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2975_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_,
                    v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_,
                );
                if lean_obj_tag(v___x_2975_) == 0 {
                    v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
                    v_isSharedCheck_2984_ = (!lean_is_exclusive(v___x_2975_)) as u8;
                    if v_isSharedCheck_2984_ == 0 {
                        v___x_2978_ = v___x_2975_;
                        v_isShared_2979_ = v_isSharedCheck_2984_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2976_);
                        lean_dec(v___x_2975_);
                        v___x_2978_ = lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2984_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2985_ = lean_ctor_get(v___x_2975_, 0);
                    v_isSharedCheck_2992_ = (!lean_is_exclusive(v___x_2975_)) as u8;
                    if v_isSharedCheck_2992_ == 0 {
                        v___x_2987_ = v___x_2975_;
                        v_isShared_2988_ = v_isSharedCheck_2992_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2985_);
                        lean_dec(v___x_2975_);
                        v___x_2987_ = lean_box(0);
                        v_isShared_2988_ = v_isSharedCheck_2992_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_op_2980_ = lean_ctor_get(v_a_2976_, 3);
                lean_inc_ref(v_op_2980_);
                lean_dec(v_a_2976_);
                if v_isShared_2979_ == 0 {
                    lean_ctor_set(v___x_2978_, 0, v_op_2980_);
                    v___x_2982_ = v___x_2978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_op_2980_);
                    v___x_2982_ = v_reuseFailAlloc_2983_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2982_;
            }
            3 => {
                if v_isShared_2988_ == 0 {
                    v___x_2990_ = v___x_2987_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
                    v___x_2990_ = v_reuseFailAlloc_2991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOp___boxed(
    mut v_a_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_a_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
    mut v_a_3000_: *mut LeanObject,
    mut v_a_3001_: *mut LeanObject,
    mut v_a_3002_: *mut LeanObject,
    mut v_a_3003_: *mut LeanObject,
    mut v_a_3004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3005_: *mut LeanObject = core::ptr::null_mut();
    v_res_3005_ = l_Lean_Meta_Grind_AC_getOp(
        v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
        v_a_3001_, v_a_3002_, v_a_3003_,
    );
    lean_dec(v_a_3003_);
    lean_dec_ref(v_a_3002_);
    lean_dec(v_a_3001_);
    lean_dec_ref(v_a_3000_);
    lean_dec(v_a_2999_);
    lean_dec_ref(v_a_2998_);
    lean_dec(v_a_2997_);
    lean_dec_ref(v_a_2996_);
    lean_dec(v_a_2995_);
    lean_dec(v_a_2994_);
    lean_dec(v_a_2993_);
    return v_res_3005_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u64 = 0;
    v___x_3006_ = lean_unsigned_to_nat(1723);
    v___x_3007_ = lean_uint64_of_nat(v___x_3006_);
    return v___x_3007_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_x_3008_: *mut LeanObject,
    mut v_x_3009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: u64 = 0;
    let mut v___x_3019_: u64 = 0;
    let mut v___x_3020_: u64 = 0;
    let mut v_fold_3021_: u64 = 0;
    let mut v___x_3022_: u64 = 0;
    let mut v___x_3023_: u64 = 0;
    let mut v___x_3024_: u64 = 0;
    let mut v___x_3025_: usize = 0;
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: usize = 0;
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: u64 = 0;
    let mut v_hash_3037_: u64 = 0;
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3009_) == 0 {
                    return v_x_3008_;
                } else {
                    v_key_3010_ = lean_ctor_get(v_x_3009_, 0);
                    v_value_3011_ = lean_ctor_get(v_x_3009_, 1);
                    v_tail_3012_ = lean_ctor_get(v_x_3009_, 2);
                    v_isSharedCheck_3038_ = (!lean_is_exclusive(v_x_3009_)) as u8;
                    if v_isSharedCheck_3038_ == 0 {
                        v___x_3014_ = v_x_3009_;
                        v_isShared_3015_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3012_);
                        lean_inc(v_value_3011_);
                        lean_inc(v_key_3010_);
                        lean_dec(v_x_3009_);
                        v___x_3014_ = lean_box(0);
                        v_isShared_3015_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3016_ = lean_array_get_size(v_x_3008_);
                if lean_obj_tag(v_key_3010_) == 0 {
                    v___x_3036_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_3018_ = v___x_3036_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3037_ = lean_ctor_get_uint64(
                        v_key_3010_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3018_ = v_hash_3037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3019_ = 32u64;
                v___x_3020_ = lean_uint64_shift_right(v___y_3018_, v___x_3019_);
                v_fold_3021_ = lean_uint64_xor(v___y_3018_, v___x_3020_);
                v___x_3022_ = 16u64;
                v___x_3023_ = lean_uint64_shift_right(v_fold_3021_, v___x_3022_);
                v___x_3024_ = lean_uint64_xor(v_fold_3021_, v___x_3023_);
                v___x_3025_ = lean_uint64_to_usize(v___x_3024_);
                v___x_3026_ = lean_usize_of_nat(v___x_3016_);
                v___x_3027_ = 1usize;
                v___x_3028_ = lean_usize_sub(v___x_3026_, v___x_3027_);
                v___x_3029_ = lean_usize_land(v___x_3025_, v___x_3028_);
                v___x_3030_ = lean_array_uget_borrowed(v_x_3008_, v___x_3029_);
                lean_inc(v___x_3030_);
                if v_isShared_3015_ == 0 {
                    lean_ctor_set(v___x_3014_, 2, v___x_3030_);
                    v___x_3032_ = v___x_3014_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_key_3010_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_value_3011_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 2, v___x_3030_);
                    v___x_3032_ = v_reuseFailAlloc_3035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3033_ = lean_array_uset(v_x_3008_, v___x_3029_, v___x_3032_);
                v_x_3008_ = v___x_3033_;
                v_x_3009_ = v_tail_3012_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_i_3039_: *mut LeanObject,
    mut v_source_3040_: *mut LeanObject,
    mut v_target_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v_es_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3042_ = lean_array_get_size(v_source_3040_);
                v___x_3043_ = lean_nat_dec_lt(v_i_3039_, v___x_3042_);
                if v___x_3043_ == 0 {
                    lean_dec_ref(v_source_3040_);
                    lean_dec(v_i_3039_);
                    return v_target_3041_;
                } else {
                    v_es_3044_ = lean_array_fget(v_source_3040_, v_i_3039_);
                    v___x_3045_ = lean_box(0);
                    v_source_3046_ = lean_array_fset(v_source_3040_, v_i_3039_, v___x_3045_);
                    v_target_3047_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_3041_, v_es_3044_);
                    v___x_3048_ = lean_unsigned_to_nat(1);
                    v___x_3049_ = lean_nat_add(v_i_3039_, v___x_3048_);
                    lean_dec(v_i_3039_);
                    v_i_3039_ = v___x_3049_;
                    v_source_3040_ = v_source_3046_;
                    v_target_3041_ = v_target_3047_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(
    mut v_data_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    v___x_3052_ = lean_array_get_size(v_data_3051_);
    v___x_3053_ = lean_unsigned_to_nat(2);
    v_nbuckets_3054_ = lean_nat_mul(v___x_3052_, v___x_3053_);
    v___x_3055_ = lean_unsigned_to_nat(0);
    v___x_3056_ = lean_box(0);
    v___x_3057_ = lean_mk_array(v_nbuckets_3054_, v___x_3056_);
    v___x_3058_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v___x_3055_, v_data_3051_, v___x_3057_);
    return v___x_3058_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(
    mut v_a_3059_: *mut LeanObject,
    mut v_x_3060_: *mut LeanObject,
) -> u8 {
    let mut v___x_3061_: u8 = 0;
    let mut v_key_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3060_) == 0 {
                    v___x_3061_ = 0;
                    return v___x_3061_;
                } else {
                    v_key_3062_ = lean_ctor_get(v_x_3060_, 0);
                    v_tail_3063_ = lean_ctor_get(v_x_3060_, 2);
                    v___x_3064_ = lean_name_eq(v_key_3062_, v_a_3059_);
                    if v___x_3064_ == 0 {
                        v_x_3060_ = v_tail_3063_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3064_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_3066_: *mut LeanObject,
    mut v_x_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3068_: u8 = 0;
    let mut v_r_3069_: *mut LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_3066_, v_x_3067_);
    lean_dec(v_x_3067_);
    lean_dec(v_a_3066_);
    v_r_3069_ = lean_box((v_res_3068_) as usize);
    return v_r_3069_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(
    mut v_m_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_b_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: u64 = 0;
    let mut v___x_3078_: u64 = 0;
    let mut v___x_3079_: u64 = 0;
    let mut v_fold_3080_: u64 = 0;
    let mut v___x_3081_: u64 = 0;
    let mut v___x_3082_: u64 = 0;
    let mut v___x_3083_: u64 = 0;
    let mut v___x_3084_: usize = 0;
    let mut v___x_3085_: usize = 0;
    let mut v___x_3086_: usize = 0;
    let mut v___x_3087_: usize = 0;
    let mut v___x_3088_: usize = 0;
    let mut v_bkt_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v_val_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_unused_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u64 = 0;
    let mut v_hash_3115_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3073_ = lean_ctor_get(v_m_3070_, 0);
                v_buckets_3074_ = lean_ctor_get(v_m_3070_, 1);
                v___x_3075_ = lean_array_get_size(v_buckets_3074_);
                if lean_obj_tag(v_a_3071_) == 0 {
                    v___x_3114_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_3077_ = v___x_3114_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3115_ = lean_ctor_get_uint64(
                        v_a_3071_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3077_ = v_hash_3115_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3078_ = 32u64;
                v___x_3079_ = lean_uint64_shift_right(v___y_3077_, v___x_3078_);
                v_fold_3080_ = lean_uint64_xor(v___y_3077_, v___x_3079_);
                v___x_3081_ = 16u64;
                v___x_3082_ = lean_uint64_shift_right(v_fold_3080_, v___x_3081_);
                v___x_3083_ = lean_uint64_xor(v_fold_3080_, v___x_3082_);
                v___x_3084_ = lean_uint64_to_usize(v___x_3083_);
                v___x_3085_ = lean_usize_of_nat(v___x_3075_);
                v___x_3086_ = 1usize;
                v___x_3087_ = lean_usize_sub(v___x_3085_, v___x_3086_);
                v___x_3088_ = lean_usize_land(v___x_3084_, v___x_3087_);
                v_bkt_3089_ = lean_array_uget_borrowed(v_buckets_3074_, v___x_3088_);
                v___x_3090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_3071_, v_bkt_3089_);
                if v___x_3090_ == 0 {
                    lean_inc_ref(v_buckets_3074_);
                    lean_inc(v_size_3073_);
                    v_isSharedCheck_3111_ = (!lean_is_exclusive(v_m_3070_)) as u8;
                    if v_isSharedCheck_3111_ == 0 {
                        v_unused_3112_ = lean_ctor_get(v_m_3070_, 1);
                        lean_dec(v_unused_3112_);
                        v_unused_3113_ = lean_ctor_get(v_m_3070_, 0);
                        lean_dec(v_unused_3113_);
                        v___x_3092_ = v_m_3070_;
                        v_isShared_3093_ = v_isSharedCheck_3111_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_3070_);
                        v___x_3092_ = lean_box(0);
                        v_isShared_3093_ = v_isSharedCheck_3111_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_3072_);
                    lean_dec(v_a_3071_);
                    return v_m_3070_;
                }
            }
            2 => {
                v___x_3094_ = lean_unsigned_to_nat(1);
                v_size_x27_3095_ = lean_nat_add(v_size_3073_, v___x_3094_);
                lean_dec(v_size_3073_);
                lean_inc(v_bkt_3089_);
                v___x_3096_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3096_, 0, v_a_3071_);
                lean_ctor_set(v___x_3096_, 1, v_b_3072_);
                lean_ctor_set(v___x_3096_, 2, v_bkt_3089_);
                v_buckets_x27_3097_ = lean_array_uset(v_buckets_3074_, v___x_3088_, v___x_3096_);
                v___x_3098_ = lean_unsigned_to_nat(4);
                v___x_3099_ = lean_nat_mul(v_size_x27_3095_, v___x_3098_);
                v___x_3100_ = lean_unsigned_to_nat(3);
                v___x_3101_ = lean_nat_div(v___x_3099_, v___x_3100_);
                lean_dec(v___x_3099_);
                v___x_3102_ = lean_array_get_size(v_buckets_x27_3097_);
                v___x_3103_ = lean_nat_dec_le(v___x_3101_, v___x_3102_);
                lean_dec(v___x_3101_);
                if v___x_3103_ == 0 {
                    v_val_3104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_buckets_x27_3097_);
                    if v_isShared_3093_ == 0 {
                        lean_ctor_set(v___x_3092_, 1, v_val_3104_);
                        lean_ctor_set(v___x_3092_, 0, v_size_x27_3095_);
                        v___x_3106_ = v___x_3092_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_size_x27_3095_);
                        lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_val_3104_);
                        v___x_3106_ = v_reuseFailAlloc_3107_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3093_ == 0 {
                        lean_ctor_set(v___x_3092_, 1, v_buckets_x27_3097_);
                        lean_ctor_set(v___x_3092_, 0, v_size_x27_3095_);
                        v___x_3109_ = v___x_3092_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_size_x27_3095_);
                        lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_buckets_x27_3097_);
                        v___x_3109_ = v_reuseFailAlloc_3110_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3106_;
            }
            4 => {
                return v___x_3109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(
    mut v_as_x27_3116_: *mut LeanObject,
    mut v_b_3117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3116_) == 0 {
                    return v_b_3117_;
                } else {
                    v_head_3118_ = lean_ctor_get(v_as_x27_3116_, 0);
                    v_tail_3119_ = lean_ctor_get(v_as_x27_3116_, 1);
                    v___x_3120_ = lean_box(0);
                    lean_inc(v_head_3118_);
                    v_r_3121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_b_3117_, v_head_3118_, v___x_3120_);
                    v_as_x27_3116_ = v_tail_3119_;
                    v_b_3117_ = v_r_3121_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(
    mut v_as_x27_3123_: *mut LeanObject,
    mut v_b_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3125_: *mut LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_3123_, v_b_3124_);
    lean_dec(v_as_x27_3123_);
    return v_res_3125_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(
    mut v_m_3126_: *mut LeanObject,
    mut v_l_3127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    v___x_3128_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_l_3127_, v_m_3126_);
    return v___x_3128_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0___boxed(
    mut v_m_3129_: *mut LeanObject,
    mut v_l_3130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3131_: *mut LeanObject = core::ptr::null_mut();
    v_res_3131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(v_m_3129_, v_l_3130_);
    lean_dec(v_l_3130_);
    return v_res_3131_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37()
-> *mut LeanObject {
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    v___x_3206_ = lean_box(0);
    v___x_3207_ = lean_unsigned_to_nat(16);
    v___x_3208_ = lean_mk_array(v___x_3207_, v___x_3206_);
    return v___x_3208_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38()
-> *mut LeanObject {
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    v___x_3209_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37);
    v___x_3210_ = lean_unsigned_to_nat(0);
    v___x_3211_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3211_, 0, v___x_3210_);
    lean_ctor_set(v___x_3211_, 1, v___x_3209_);
    return v___x_3211_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39()
-> *mut LeanObject {
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    v___x_3212_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38);
    v___x_3213_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36;
    v___x_3214_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v___x_3213_, v___x_3212_);
    return v___x_3214_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc()
-> *mut LeanObject {
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    v___x_3215_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39);
    return v___x_3215_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(
    mut v_00_u03b2_3216_: *mut LeanObject,
    mut v_m_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_b_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_3217_, v_a_3218_, v_b_3219_);
    return v___x_3220_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(
    mut v_as_3221_: *mut LeanObject,
    mut v_as_x27_3222_: *mut LeanObject,
    mut v_b_3223_: *mut LeanObject,
    mut v_a_3224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    v___x_3225_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_3222_, v_b_3223_);
    return v___x_3225_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(
    mut v_as_3226_: *mut LeanObject,
    mut v_as_x27_3227_: *mut LeanObject,
    mut v_b_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3230_: *mut LeanObject = core::ptr::null_mut();
    v_res_3230_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(v_as_3226_, v_as_x27_3227_, v_b_3228_, v_a_3229_);
    lean_dec(v_as_x27_3227_);
    lean_dec(v_as_3226_);
    return v_res_3230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3231_: *mut LeanObject,
    mut v_a_3232_: *mut LeanObject,
    mut v_x_3233_: *mut LeanObject,
) -> u8 {
    let mut v___x_3234_: u8 = 0;
    v___x_3234_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_3232_, v_x_3233_);
    return v___x_3234_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
    mut v_x_3237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3238_: u8 = 0;
    let mut v_r_3239_: *mut LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(v_00_u03b2_3235_, v_a_3236_, v_x_3237_);
    lean_dec(v_x_3237_);
    lean_dec(v_a_3236_);
    v_r_3239_ = lean_box((v_res_3238_) as usize);
    return v_r_3239_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3240_: *mut LeanObject,
    mut v_data_3241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_data_3241_);
    return v___x_3242_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_3243_: *mut LeanObject,
    mut v_i_3244_: *mut LeanObject,
    mut v_source_3245_: *mut LeanObject,
    mut v_target_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    v___x_3247_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v_i_3244_, v_source_3245_, v_target_3246_);
    return v___x_3247_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b2_3248_: *mut LeanObject,
    mut v_x_3249_: *mut LeanObject,
    mut v_x_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_3249_, v_x_3250_);
    return v___x_3251_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(
    mut v_op_3277_: *mut LeanObject,
    mut v_f_3278_: *mut LeanObject,
    mut v_a_3279_: *mut LeanObject,
    mut v_a_3280_: *mut LeanObject,
    mut v_a_3281_: *mut LeanObject,
    mut v_a_3282_: *mut LeanObject,
    mut v_a_3283_: *mut LeanObject,
    mut v_a_3284_: *mut LeanObject,
    mut v_a_3285_: *mut LeanObject,
    mut v_a_3286_: *mut LeanObject,
    mut v_a_3287_: *mut LeanObject,
    mut v_a_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v_ring_3299_: u8 = 0;
    let mut v___y_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3302_: u8 = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut v_a_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3316_: u8 = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3320_: u8 = 0;
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3337_: u8 = 0;
    let mut v_a_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: u8 = 0;
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: u8 = 0;
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3366_: u8 = 0;
    let mut v_a_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3294_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3281_);
                if lean_obj_tag(v___x_3294_) == 0 {
                    v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3366_ = (!lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3366_ == 0 {
                        v___x_3297_ = v___x_3294_;
                        v_isShared_3298_ = v_isSharedCheck_3366_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3295_);
                        lean_dec(v___x_3294_);
                        v___x_3297_ = lean_box(0);
                        v_isShared_3298_ = v_isSharedCheck_3366_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3367_ = lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3374_ = (!lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3374_ == 0 {
                        v___x_3369_ = v___x_3294_;
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3367_);
                        lean_dec(v___x_3294_);
                        v___x_3369_ = lean_box(0);
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3291_ = 0;
                v___x_3292_ = lean_box((v___x_3291_) as usize);
                v___x_3293_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3293_, 0, v___x_3292_);
                return v___x_3293_;
            }
            2 => {
                v_ring_3299_ = lean_ctor_get_uint8(
                    v_a_3295_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 21) as u32,
                );
                lean_dec(v_a_3295_);
                if v_ring_3299_ == 0 {
                    v___x_3346_ = lean_box((v_ring_3299_) as usize);
                    if v_isShared_3298_ == 0 {
                        lean_ctor_set(v___x_3297_, 0, v___x_3346_);
                        v___x_3348_ = v___x_3297_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
                        v___x_3348_ = v_reuseFailAlloc_3349_;
                        state = 13;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_f_3278_) == 4 {
                        lean_del_object(v___x_3297_);
                        v_declName_3350_ = lean_ctor_get(v_f_3278_, 0);
                        v___x_3351_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2;
                        v___x_3352_ = lean_name_eq(v_declName_3350_, v___x_3351_);
                        if v___x_3352_ == 0 {
                            v___x_3353_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5;
                            v___x_3354_ = lean_name_eq(v_declName_3350_, v___x_3353_);
                            if v___x_3354_ == 0 {
                                v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8;
                                v___x_3356_ = lean_name_eq(v_declName_3350_, v___x_3355_);
                                if v___x_3356_ == 0 {
                                    v___x_3357_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11;
                                    v___x_3358_ = lean_name_eq(v_declName_3350_, v___x_3357_);
                                    if v___x_3358_ == 0 {
                                        v___x_3359_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14;
                                        v___x_3360_ = lean_name_eq(v_declName_3350_, v___x_3359_);
                                        if v___x_3360_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            state = 8;
                                            continue;
                                        }
                                    } else {
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    state = 8;
                                    continue;
                                }
                            } else {
                                state = 8;
                                continue;
                            }
                        } else {
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_3361_ = 0;
                        v___x_3362_ = lean_box((v___x_3361_) as usize);
                        if v_isShared_3298_ == 0 {
                            lean_ctor_set(v___x_3297_, 0, v___x_3362_);
                            v___x_3364_ = v___x_3297_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
                            v___x_3364_ = v_reuseFailAlloc_3365_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_3303_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(
                    v___y_3301_,
                    v_a_3279_,
                    v_a_3280_,
                    v_a_3281_,
                    v_a_3282_,
                    v_a_3283_,
                    v_a_3284_,
                    v_a_3285_,
                    v_a_3286_,
                    v_a_3287_,
                    v_a_3288_,
                );
                if lean_obj_tag(v___x_3303_) == 0 {
                    v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
                    v_isSharedCheck_3312_ = (!lean_is_exclusive(v___x_3303_)) as u8;
                    if v_isSharedCheck_3312_ == 0 {
                        v___x_3306_ = v___x_3303_;
                        v_isShared_3307_ = v_isSharedCheck_3312_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3304_);
                        lean_dec(v___x_3303_);
                        v___x_3306_ = lean_box(0);
                        v_isShared_3307_ = v_isSharedCheck_3312_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_3313_ = lean_ctor_get(v___x_3303_, 0);
                    v_isSharedCheck_3320_ = (!lean_is_exclusive(v___x_3303_)) as u8;
                    if v_isSharedCheck_3320_ == 0 {
                        v___x_3315_ = v___x_3303_;
                        v_isShared_3316_ = v_isSharedCheck_3320_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3313_);
                        lean_dec(v___x_3303_);
                        v___x_3315_ = lean_box(0);
                        v_isShared_3316_ = v_isSharedCheck_3320_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_3304_) == 0 {
                    lean_del_object(v___x_3306_);
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_a_3304_, 1);
                    if v___y_3302_ == 0 {
                        lean_del_object(v___x_3306_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3308_ = lean_box((v_ring_3299_) as usize);
                        if v_isShared_3307_ == 0 {
                            lean_ctor_set(v___x_3306_, 0, v___x_3308_);
                            v___x_3310_ = v___x_3306_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
                            v___x_3310_ = v_reuseFailAlloc_3311_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_3310_;
            }
            6 => {
                if v_isShared_3316_ == 0 {
                    v___x_3318_ = v___x_3315_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
                    v___x_3318_ = v_reuseFailAlloc_3319_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3318_;
            }
            8 => {
                v___x_3322_ = l_Lean_Expr_getAppNumArgs(v_op_3277_);
                v___x_3323_ = lean_unsigned_to_nat(4);
                v___x_3324_ = lean_nat_dec_eq(v___x_3322_, v___x_3323_);
                lean_dec(v___x_3322_);
                if v___x_3324_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3325_ = l_Lean_Expr_appFn_x21(v_op_3277_);
                    v___x_3326_ = l_Lean_Expr_appFn_x21(v___x_3325_);
                    lean_dec_ref(v___x_3325_);
                    v___x_3327_ = l_Lean_Expr_appArg_x21(v___x_3326_);
                    lean_dec_ref(v___x_3326_);
                    lean_inc_ref(v___x_3327_);
                    v___x_3328_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                        v___x_3327_,
                        v_a_3279_,
                        v_a_3280_,
                        v_a_3281_,
                        v_a_3282_,
                        v_a_3283_,
                        v_a_3284_,
                        v_a_3285_,
                        v_a_3286_,
                        v_a_3287_,
                        v_a_3288_,
                    );
                    if lean_obj_tag(v___x_3328_) == 0 {
                        v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
                        v_isSharedCheck_3337_ = (!lean_is_exclusive(v___x_3328_)) as u8;
                        if v_isSharedCheck_3337_ == 0 {
                            v___x_3331_ = v___x_3328_;
                            v_isShared_3332_ = v_isSharedCheck_3337_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3329_);
                            lean_dec(v___x_3328_);
                            v___x_3331_ = lean_box(0);
                            v_isShared_3332_ = v_isSharedCheck_3337_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3327_);
                        v_a_3338_ = lean_ctor_get(v___x_3328_, 0);
                        v_isSharedCheck_3345_ = (!lean_is_exclusive(v___x_3328_)) as u8;
                        if v_isSharedCheck_3345_ == 0 {
                            v___x_3340_ = v___x_3328_;
                            v_isShared_3341_ = v_isSharedCheck_3345_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3338_);
                            lean_dec(v___x_3328_);
                            v___x_3340_ = lean_box(0);
                            v_isShared_3341_ = v_isSharedCheck_3345_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if lean_obj_tag(v_a_3329_) == 0 {
                    lean_del_object(v___x_3331_);
                    v___y_3301_ = v___x_3327_;
                    v___y_3302_ = v___x_3324_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref_known(v_a_3329_, 1);
                    if v___x_3324_ == 0 {
                        lean_del_object(v___x_3331_);
                        v___y_3301_ = v___x_3327_;
                        v___y_3302_ = v___x_3324_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref(v___x_3327_);
                        v___x_3333_ = lean_box((v_ring_3299_) as usize);
                        if v_isShared_3332_ == 0 {
                            lean_ctor_set(v___x_3331_, 0, v___x_3333_);
                            v___x_3335_ = v___x_3331_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
                            v___x_3335_ = v_reuseFailAlloc_3336_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            10 => {
                return v___x_3335_;
            }
            11 => {
                if v_isShared_3341_ == 0 {
                    v___x_3343_ = v___x_3340_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
                    v___x_3343_ = v_reuseFailAlloc_3344_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3343_;
            }
            13 => {
                return v___x_3348_;
            }
            14 => {
                return v___x_3364_;
            }
            15 => {
                if v_isShared_3370_ == 0 {
                    v___x_3372_ = v___x_3369_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
                    v___x_3372_ = v_reuseFailAlloc_3373_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(
    mut v_op_3375_: *mut LeanObject,
    mut v_f_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
    mut v_a_3379_: *mut LeanObject,
    mut v_a_3380_: *mut LeanObject,
    mut v_a_3381_: *mut LeanObject,
    mut v_a_3382_: *mut LeanObject,
    mut v_a_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
    mut v_a_3386_: *mut LeanObject,
    mut v_a_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3388_: *mut LeanObject = core::ptr::null_mut();
    v_res_3388_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(
            v_op_3375_, v_f_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_,
            v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_,
        );
    lean_dec(v_a_3386_);
    lean_dec_ref(v_a_3385_);
    lean_dec(v_a_3384_);
    lean_dec_ref(v_a_3383_);
    lean_dec(v_a_3382_);
    lean_dec_ref(v_a_3381_);
    lean_dec(v_a_3380_);
    lean_dec_ref(v_a_3379_);
    lean_dec(v_a_3378_);
    lean_dec(v_a_3377_);
    lean_dec_ref(v_f_3376_);
    lean_dec_ref(v_op_3375_);
    return v_res_3388_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3389_: *mut LeanObject,
    mut v_vals_3390_: *mut LeanObject,
    mut v_i_3391_: *mut LeanObject,
    mut v_k_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3393_ = lean_array_get_size(v_keys_3389_);
                v___x_3394_ = lean_nat_dec_lt(v_i_3391_, v___x_3393_);
                if v___x_3394_ == 0 {
                    lean_dec(v_i_3391_);
                    v___x_3395_ = lean_box(0);
                    return v___x_3395_;
                } else {
                    v_k_x27_3396_ = lean_array_fget_borrowed(v_keys_3389_, v_i_3391_);
                    v___x_3397_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3392_,
                            v_k_x27_3396_,
                        );
                    if v___x_3397_ == 0 {
                        v___x_3398_ = lean_unsigned_to_nat(1);
                        v___x_3399_ = lean_nat_add(v_i_3391_, v___x_3398_);
                        lean_dec(v_i_3391_);
                        v_i_3391_ = v___x_3399_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3401_ = lean_array_fget_borrowed(v_vals_3390_, v_i_3391_);
                        lean_dec(v_i_3391_);
                        lean_inc(v___x_3401_);
                        v___x_3402_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3402_, 0, v___x_3401_);
                        return v___x_3402_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3403_: *mut LeanObject,
    mut v_vals_3404_: *mut LeanObject,
    mut v_i_3405_: *mut LeanObject,
    mut v_k_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3407_: *mut LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_3403_, v_vals_3404_, v_i_3405_, v_k_3406_);
    lean_dec_ref(v_k_3406_);
    lean_dec_ref(v_vals_3404_);
    lean_dec_ref(v_keys_3403_);
    return v_res_3407_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_3408_: usize = 0;
    let mut v___x_3409_: usize = 0;
    let mut v___x_3410_: usize = 0;
    v___x_3408_ = 5usize;
    v___x_3409_ = 1usize;
    v___x_3410_ = lean_usize_shift_left(v___x_3409_, v___x_3408_);
    return v___x_3410_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_3411_: usize = 0;
    let mut v___x_3412_: usize = 0;
    let mut v___x_3413_: usize = 0;
    v___x_3411_ = 1usize;
    v___x_3412_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0);
    v___x_3413_ = lean_usize_sub(v___x_3412_, v___x_3411_);
    return v___x_3413_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(
    mut v_x_3414_: *mut LeanObject,
    mut v_x_3415_: usize,
    mut v_x_3416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: usize = 0;
    let mut v___x_3420_: usize = 0;
    let mut v___x_3421_: usize = 0;
    let mut v_j_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: usize = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3414_) == 0 {
                    v_es_3417_ = lean_ctor_get(v_x_3414_, 0);
                    v___x_3418_ = lean_box(2);
                    v___x_3419_ = 5usize;
                    v___x_3420_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1);
                    v___x_3421_ = lean_usize_land(v_x_3415_, v___x_3420_);
                    v_j_3422_ = lean_usize_to_nat(v___x_3421_);
                    v___x_3423_ = lean_array_get_borrowed(v___x_3418_, v_es_3417_, v_j_3422_);
                    lean_dec(v_j_3422_);
                    match lean_obj_tag(v___x_3423_) {
                        0 => {
                            v_key_3424_ = lean_ctor_get(v___x_3423_, 0);
                            v_val_3425_ = lean_ctor_get(v___x_3423_, 1);
                            v___x_3426_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3416_, v_key_3424_);
                            if v___x_3426_ == 0 {
                                v___x_3427_ = lean_box(0);
                                return v___x_3427_;
                            } else {
                                lean_inc(v_val_3425_);
                                v___x_3428_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3428_, 0, v_val_3425_);
                                return v___x_3428_;
                            }
                        }
                        1 => {
                            v_node_3429_ = lean_ctor_get(v___x_3423_, 0);
                            v___x_3430_ = lean_usize_shift_right(v_x_3415_, v___x_3419_);
                            v_x_3414_ = v_node_3429_;
                            v_x_3415_ = v___x_3430_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3432_ = lean_box(0);
                            return v___x_3432_;
                        }
                    }
                } else {
                    v_ks_3433_ = lean_ctor_get(v_x_3414_, 0);
                    v_vs_3434_ = lean_ctor_get(v_x_3414_, 1);
                    v___x_3435_ = lean_unsigned_to_nat(0);
                    v___x_3436_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_ks_3433_, v_vs_3434_, v___x_3435_, v_x_3416_);
                    return v___x_3436_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(
    mut v_x_3437_: *mut LeanObject,
    mut v_x_3438_: *mut LeanObject,
    mut v_x_3439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_949__boxed_3440_: usize = 0;
    let mut v_res_3441_: *mut LeanObject = core::ptr::null_mut();
    v_x_949__boxed_3440_ = lean_unbox_usize(v_x_3438_);
    lean_dec(v_x_3438_);
    v_res_3441_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_3437_, v_x_949__boxed_3440_, v_x_3439_);
    lean_dec_ref(v_x_3439_);
    lean_dec_ref(v_x_3437_);
    return v_res_3441_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
    mut v_x_3442_: *mut LeanObject,
    mut v_x_3443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3444_: u64 = 0;
    let mut v___x_3445_: usize = 0;
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3443_);
    v___x_3445_ = lean_uint64_to_usize(v___x_3444_);
    v___x_3446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_3442_, v___x_3445_, v_x_3443_);
    return v___x_3446_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(
    mut v_x_3447_: *mut LeanObject,
    mut v_x_3448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3449_: *mut LeanObject = core::ptr::null_mut();
    v_res_3449_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
            v_x_3447_, v_x_3448_,
        );
    lean_dec_ref(v_x_3448_);
    lean_dec_ref(v_x_3447_);
    return v_res_3449_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds___redArg(
    mut v_e_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v_a_3452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v_exprToOpIds_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_a_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3454_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_3451_, v_a_3452_);
                if lean_obj_tag(v___x_3454_) == 0 {
                    v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
                    v_isSharedCheck_3469_ = (!lean_is_exclusive(v___x_3454_)) as u8;
                    if v_isSharedCheck_3469_ == 0 {
                        v___x_3457_ = v___x_3454_;
                        v_isShared_3458_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3455_);
                        lean_dec(v___x_3454_);
                        v___x_3457_ = lean_box(0);
                        v_isShared_3458_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3470_ = lean_ctor_get(v___x_3454_, 0);
                    v_isSharedCheck_3477_ = (!lean_is_exclusive(v___x_3454_)) as u8;
                    if v_isSharedCheck_3477_ == 0 {
                        v___x_3472_ = v___x_3454_;
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3470_);
                        lean_dec(v___x_3454_);
                        v___x_3472_ = lean_box(0);
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToOpIds_3459_ = lean_ctor_get(v_a_3455_, 2);
                lean_inc_ref(v_exprToOpIds_3459_);
                lean_dec(v_a_3455_);
                v___x_3460_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_exprToOpIds_3459_, v_e_3450_);
                lean_dec_ref(v_exprToOpIds_3459_);
                if lean_obj_tag(v___x_3460_) == 0 {
                    v___x_3461_ = lean_box(0);
                    if v_isShared_3458_ == 0 {
                        lean_ctor_set(v___x_3457_, 0, v___x_3461_);
                        v___x_3463_ = v___x_3457_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3465_ = lean_ctor_get(v___x_3460_, 0);
                    lean_inc(v_val_3465_);
                    lean_dec_ref_known(v___x_3460_, 1);
                    if v_isShared_3458_ == 0 {
                        lean_ctor_set(v___x_3457_, 0, v_val_3465_);
                        v___x_3467_ = v___x_3457_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_val_3465_);
                        v___x_3467_ = v_reuseFailAlloc_3468_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3463_;
            }
            3 => {
                return v___x_3467_;
            }
            4 => {
                if v_isShared_3473_ == 0 {
                    v___x_3475_ = v___x_3472_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
                    v___x_3475_ = v_reuseFailAlloc_3476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(
    mut v_e_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
    mut v_a_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3482_: *mut LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_3478_, v_a_3479_, v_a_3480_);
    lean_dec_ref(v_a_3480_);
    lean_dec(v_a_3479_);
    lean_dec_ref(v_e_3478_);
    return v_res_3482_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds(
    mut v_e_3483_: *mut LeanObject,
    mut v_a_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
    mut v_a_3487_: *mut LeanObject,
    mut v_a_3488_: *mut LeanObject,
    mut v_a_3489_: *mut LeanObject,
    mut v_a_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_3483_, v_a_3484_, v_a_3492_);
    return v___x_3495_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds___boxed(
    mut v_e_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
    mut v_a_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
    mut v_a_3506_: *mut LeanObject,
    mut v_a_3507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3508_: *mut LeanObject = core::ptr::null_mut();
    v_res_3508_ = l_Lean_Meta_Grind_AC_getTermOpIds(
        v_e_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_,
        v_a_3504_, v_a_3505_, v_a_3506_,
    );
    lean_dec(v_a_3506_);
    lean_dec_ref(v_a_3505_);
    lean_dec(v_a_3504_);
    lean_dec_ref(v_a_3503_);
    lean_dec(v_a_3502_);
    lean_dec_ref(v_a_3501_);
    lean_dec(v_a_3500_);
    lean_dec_ref(v_a_3499_);
    lean_dec(v_a_3498_);
    lean_dec(v_a_3497_);
    lean_dec_ref(v_e_3496_);
    return v_res_3508_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(
    mut v_00_u03b2_3509_: *mut LeanObject,
    mut v_x_3510_: *mut LeanObject,
    mut v_x_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    v___x_3512_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
            v_x_3510_, v_x_3511_,
        );
    return v___x_3512_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(
    mut v_00_u03b2_3513_: *mut LeanObject,
    mut v_x_3514_: *mut LeanObject,
    mut v_x_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3516_: *mut LeanObject = core::ptr::null_mut();
    v_res_3516_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(
            v_00_u03b2_3513_,
            v_x_3514_,
            v_x_3515_,
        );
    lean_dec_ref(v_x_3515_);
    lean_dec_ref(v_x_3514_);
    return v_res_3516_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(
    mut v_00_u03b2_3517_: *mut LeanObject,
    mut v_x_3518_: *mut LeanObject,
    mut v_x_3519_: usize,
    mut v_x_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    v___x_3521_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_3518_, v_x_3519_, v_x_3520_);
    return v___x_3521_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(
    mut v_00_u03b2_3522_: *mut LeanObject,
    mut v_x_3523_: *mut LeanObject,
    mut v_x_3524_: *mut LeanObject,
    mut v_x_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1076__boxed_3526_: usize = 0;
    let mut v_res_3527_: *mut LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_3526_ = lean_unbox_usize(v_x_3524_);
    lean_dec(v_x_3524_);
    v_res_3527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(v_00_u03b2_3522_, v_x_3523_, v_x_1076__boxed_3526_, v_x_3525_);
    lean_dec_ref(v_x_3525_);
    lean_dec_ref(v_x_3523_);
    return v_res_3527_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3528_: *mut LeanObject,
    mut v_keys_3529_: *mut LeanObject,
    mut v_vals_3530_: *mut LeanObject,
    mut v_heq_3531_: *mut LeanObject,
    mut v_i_3532_: *mut LeanObject,
    mut v_k_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    v___x_3534_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_3529_, v_vals_3530_, v_i_3532_, v_k_3533_);
    return v___x_3534_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3535_: *mut LeanObject,
    mut v_keys_3536_: *mut LeanObject,
    mut v_vals_3537_: *mut LeanObject,
    mut v_heq_3538_: *mut LeanObject,
    mut v_i_3539_: *mut LeanObject,
    mut v_k_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3541_: *mut LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(v_00_u03b2_3535_, v_keys_3536_, v_vals_3537_, v_heq_3538_, v_i_3539_, v_k_3540_);
    lean_dec_ref(v_k_3540_);
    lean_dec_ref(v_vals_3537_);
    lean_dec_ref(v_keys_3536_);
    return v_res_3541_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(
    mut v_opId_3542_: *mut LeanObject,
    mut v_a_3543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: u8 = 0;
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3551_: u8 = 0;
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_unused_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3543_) == 0 {
                    v___x_3544_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3544_, 0, v_opId_3542_);
                    lean_ctor_set(v___x_3544_, 1, v_a_3543_);
                    return v___x_3544_;
                } else {
                    v_head_3545_ = lean_ctor_get(v_a_3543_, 0);
                    v_tail_3546_ = lean_ctor_get(v_a_3543_, 1);
                    v___x_3547_ = lean_nat_dec_lt(v_opId_3542_, v_head_3545_);
                    if v___x_3547_ == 0 {
                        lean_inc(v_tail_3546_);
                        lean_inc(v_head_3545_);
                        v_isSharedCheck_3559_ = (!lean_is_exclusive(v_a_3543_)) as u8;
                        if v_isSharedCheck_3559_ == 0 {
                            v_unused_3560_ = lean_ctor_get(v_a_3543_, 1);
                            lean_dec(v_unused_3560_);
                            v_unused_3561_ = lean_ctor_get(v_a_3543_, 0);
                            lean_dec(v_unused_3561_);
                            v___x_3549_ = v_a_3543_;
                            v_isShared_3550_ = v_isSharedCheck_3559_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3543_);
                            v___x_3549_ = lean_box(0);
                            v_isShared_3550_ = v_isSharedCheck_3559_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_3562_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3562_, 0, v_opId_3542_);
                        lean_ctor_set(v___x_3562_, 1, v_a_3543_);
                        return v___x_3562_;
                    }
                }
            }
            1 => {
                v___x_3551_ = lean_nat_dec_eq(v_opId_3542_, v_head_3545_);
                if v___x_3551_ == 0 {
                    v___x_3552_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_3542_, v_tail_3546_);
                    if v_isShared_3550_ == 0 {
                        lean_ctor_set(v___x_3549_, 1, v___x_3552_);
                        v___x_3554_ = v___x_3549_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_head_3545_);
                        lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3552_);
                        v___x_3554_ = v_reuseFailAlloc_3555_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_head_3545_);
                    if v_isShared_3550_ == 0 {
                        lean_ctor_set(v___x_3549_, 0, v_opId_3542_);
                        v___x_3557_ = v___x_3549_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_opId_3542_);
                        lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_tail_3546_);
                        v___x_3557_ = v_reuseFailAlloc_3558_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3554_;
            }
            3 => {
                return v___x_3557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_3563_: *mut LeanObject,
    mut v_x_3564_: *mut LeanObject,
    mut v_x_3565_: *mut LeanObject,
    mut v_x_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: u8 = 0;
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3567_ = lean_ctor_get(v_x_3563_, 0);
                v_vs_3568_ = lean_ctor_get(v_x_3563_, 1);
                v_isSharedCheck_3592_ = (!lean_is_exclusive(v_x_3563_)) as u8;
                if v_isSharedCheck_3592_ == 0 {
                    v___x_3570_ = v_x_3563_;
                    v_isShared_3571_ = v_isSharedCheck_3592_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3568_);
                    lean_inc(v_ks_3567_);
                    lean_dec(v_x_3563_);
                    v___x_3570_ = lean_box(0);
                    v_isShared_3571_ = v_isSharedCheck_3592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3572_ = lean_array_get_size(v_ks_3567_);
                v___x_3573_ = lean_nat_dec_lt(v_x_3564_, v___x_3572_);
                if v___x_3573_ == 0 {
                    lean_dec(v_x_3564_);
                    v___x_3574_ = lean_array_push(v_ks_3567_, v_x_3565_);
                    v___x_3575_ = lean_array_push(v_vs_3568_, v_x_3566_);
                    if v_isShared_3571_ == 0 {
                        lean_ctor_set(v___x_3570_, 1, v___x_3575_);
                        lean_ctor_set(v___x_3570_, 0, v___x_3574_);
                        v___x_3577_ = v___x_3570_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3574_);
                        lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3575_);
                        v___x_3577_ = v_reuseFailAlloc_3578_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3579_ = lean_array_fget_borrowed(v_ks_3567_, v_x_3564_);
                    v___x_3580_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_3565_,
                            v_k_x27_3579_,
                        );
                    if v___x_3580_ == 0 {
                        if v_isShared_3571_ == 0 {
                            v___x_3582_ = v___x_3570_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_ks_3567_);
                            lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_vs_3568_);
                            v___x_3582_ = v_reuseFailAlloc_3586_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3587_ = lean_array_fset(v_ks_3567_, v_x_3564_, v_x_3565_);
                        v___x_3588_ = lean_array_fset(v_vs_3568_, v_x_3564_, v_x_3566_);
                        lean_dec(v_x_3564_);
                        if v_isShared_3571_ == 0 {
                            lean_ctor_set(v___x_3570_, 1, v___x_3588_);
                            lean_ctor_set(v___x_3570_, 0, v___x_3587_);
                            v___x_3590_ = v___x_3570_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3587_);
                            lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3588_);
                            v___x_3590_ = v_reuseFailAlloc_3591_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3577_;
            }
            3 => {
                v___x_3583_ = lean_unsigned_to_nat(1);
                v___x_3584_ = lean_nat_add(v_x_3564_, v___x_3583_);
                lean_dec(v_x_3564_);
                v_x_3563_ = v___x_3582_;
                v_x_3564_ = v___x_3584_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(
    mut v_n_3593_: *mut LeanObject,
    mut v_k_3594_: *mut LeanObject,
    mut v_v_3595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    v___x_3596_ = lean_unsigned_to_nat(0);
    v___x_3597_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3593_, v___x_3596_, v_k_3594_, v_v_3595_);
    return v___x_3597_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3598_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(
    mut v_x_3599_: *mut LeanObject,
    mut v_x_3600_: usize,
    mut v_x_3601_: usize,
    mut v_x_3602_: *mut LeanObject,
    mut v_x_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: usize = 0;
    let mut v___x_3606_: usize = 0;
    let mut v___x_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v_j_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v_v_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3628_: u8 = 0;
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v_node_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3640_: usize = 0;
    let mut v___x_3641_: usize = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_unused_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3659_: u8 = 0;
    let mut v_ks_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: usize = 0;
    let mut v___x_3666_: u8 = 0;
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: u8 = 0;
    let mut v_reuseFailAlloc_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3599_) == 0 {
                    v_es_3604_ = lean_ctor_get(v_x_3599_, 0);
                    v___x_3605_ = 5usize;
                    v___x_3606_ = 1usize;
                    v___x_3607_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1);
                    v___x_3608_ = lean_usize_land(v_x_3600_, v___x_3607_);
                    v_j_3609_ = lean_usize_to_nat(v___x_3608_);
                    v___x_3610_ = lean_array_get_size(v_es_3604_);
                    v___x_3611_ = lean_nat_dec_lt(v_j_3609_, v___x_3610_);
                    if v___x_3611_ == 0 {
                        lean_dec(v_j_3609_);
                        lean_dec(v_x_3603_);
                        lean_dec_ref(v_x_3602_);
                        return v_x_3599_;
                    } else {
                        lean_inc_ref(v_es_3604_);
                        v_isSharedCheck_3648_ = (!lean_is_exclusive(v_x_3599_)) as u8;
                        if v_isSharedCheck_3648_ == 0 {
                            v_unused_3649_ = lean_ctor_get(v_x_3599_, 0);
                            lean_dec(v_unused_3649_);
                            v___x_3613_ = v_x_3599_;
                            v_isShared_3614_ = v_isSharedCheck_3648_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3599_);
                            v___x_3613_ = lean_box(0);
                            v_isShared_3614_ = v_isSharedCheck_3648_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3650_ = lean_ctor_get(v_x_3599_, 0);
                    v_vs_3651_ = lean_ctor_get(v_x_3599_, 1);
                    v_isSharedCheck_3671_ = (!lean_is_exclusive(v_x_3599_)) as u8;
                    if v_isSharedCheck_3671_ == 0 {
                        v___x_3653_ = v_x_3599_;
                        v_isShared_3654_ = v_isSharedCheck_3671_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3651_);
                        lean_inc(v_ks_3650_);
                        lean_dec(v_x_3599_);
                        v___x_3653_ = lean_box(0);
                        v_isShared_3654_ = v_isSharedCheck_3671_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3615_ = lean_array_fget(v_es_3604_, v_j_3609_);
                v___x_3616_ = lean_box(0);
                v_xs_x27_3617_ = lean_array_fset(v_es_3604_, v_j_3609_, v___x_3616_);
                match lean_obj_tag(v_v_3615_) {
                    0 => {
                        v_key_3624_ = lean_ctor_get(v_v_3615_, 0);
                        v_val_3625_ = lean_ctor_get(v_v_3615_, 1);
                        v_isSharedCheck_3635_ = (!lean_is_exclusive(v_v_3615_)) as u8;
                        if v_isSharedCheck_3635_ == 0 {
                            v___x_3627_ = v_v_3615_;
                            v_isShared_3628_ = v_isSharedCheck_3635_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3625_);
                            lean_inc(v_key_3624_);
                            lean_dec(v_v_3615_);
                            v___x_3627_ = lean_box(0);
                            v_isShared_3628_ = v_isSharedCheck_3635_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3636_ = lean_ctor_get(v_v_3615_, 0);
                        v_isSharedCheck_3646_ = (!lean_is_exclusive(v_v_3615_)) as u8;
                        if v_isSharedCheck_3646_ == 0 {
                            v___x_3638_ = v_v_3615_;
                            v_isShared_3639_ = v_isSharedCheck_3646_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3636_);
                            lean_dec(v_v_3615_);
                            v___x_3638_ = lean_box(0);
                            v_isShared_3639_ = v_isSharedCheck_3646_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3647_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3647_, 0, v_x_3602_);
                        lean_ctor_set(v___x_3647_, 1, v_x_3603_);
                        v___y_3619_ = v___x_3647_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3620_ = lean_array_fset(v_xs_x27_3617_, v_j_3609_, v___y_3619_);
                lean_dec(v_j_3609_);
                if v_isShared_3614_ == 0 {
                    lean_ctor_set(v___x_3613_, 0, v___x_3620_);
                    v___x_3622_ = v___x_3613_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3622_;
            }
            4 => {
                v___x_3629_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_3602_,
                        v_key_3624_,
                    );
                if v___x_3629_ == 0 {
                    lean_del_object(v___x_3627_);
                    v___x_3630_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3624_,
                        v_val_3625_,
                        v_x_3602_,
                        v_x_3603_,
                    );
                    v___x_3631_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3631_, 0, v___x_3630_);
                    v___y_3619_ = v___x_3631_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3625_);
                    lean_dec(v_key_3624_);
                    if v_isShared_3628_ == 0 {
                        lean_ctor_set(v___x_3627_, 1, v_x_3603_);
                        lean_ctor_set(v___x_3627_, 0, v_x_3602_);
                        v___x_3633_ = v___x_3627_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_x_3602_);
                        lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_x_3603_);
                        v___x_3633_ = v_reuseFailAlloc_3634_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3619_ = v___x_3633_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3640_ = lean_usize_shift_right(v_x_3600_, v___x_3605_);
                v___x_3641_ = lean_usize_add(v_x_3601_, v___x_3606_);
                v___x_3642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_node_3636_, v___x_3640_, v___x_3641_, v_x_3602_, v_x_3603_);
                if v_isShared_3639_ == 0 {
                    lean_ctor_set(v___x_3638_, 0, v___x_3642_);
                    v___x_3644_ = v___x_3638_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3619_ = v___x_3644_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3654_ == 0 {
                    v___x_3656_ = v___x_3653_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_ks_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_vs_3651_);
                    v___x_3656_ = v_reuseFailAlloc_3670_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3657_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v___x_3656_, v_x_3602_, v_x_3603_);
                v___x_3665_ = 7usize;
                v___x_3666_ = lean_usize_dec_le(v___x_3665_, v_x_3601_);
                if v___x_3666_ == 0 {
                    v___x_3667_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3657_);
                    v___x_3668_ = lean_unsigned_to_nat(4);
                    v___x_3669_ = lean_nat_dec_lt(v___x_3667_, v___x_3668_);
                    lean_dec(v___x_3667_);
                    v___y_3659_ = v___x_3669_;
                    state = 10;
                    continue;
                } else {
                    v___y_3659_ = v___x_3666_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3659_ == 0 {
                    v_ks_3660_ = lean_ctor_get(v_newNode_3657_, 0);
                    lean_inc_ref(v_ks_3660_);
                    v_vs_3661_ = lean_ctor_get(v_newNode_3657_, 1);
                    lean_inc_ref(v_vs_3661_);
                    lean_dec_ref(v_newNode_3657_);
                    v___x_3662_ = lean_unsigned_to_nat(0);
                    v___x_3663_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
                    v___x_3664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_x_3601_, v_ks_3660_, v_vs_3661_, v___x_3662_, v___x_3663_);
                    lean_dec_ref(v_vs_3661_);
                    lean_dec_ref(v_ks_3660_);
                    return v___x_3664_;
                } else {
                    return v_newNode_3657_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(
    mut v_depth_3672_: usize,
    mut v_keys_3673_: *mut LeanObject,
    mut v_vals_3674_: *mut LeanObject,
    mut v_i_3675_: *mut LeanObject,
    mut v_entries_3676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    let mut v_k_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u64 = 0;
    let mut v_h_3682_: usize = 0;
    let mut v___x_3683_: usize = 0;
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: usize = 0;
    let mut v___x_3686_: usize = 0;
    let mut v___x_3687_: usize = 0;
    let mut v_h_3688_: usize = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3677_ = lean_array_get_size(v_keys_3673_);
                v___x_3678_ = lean_nat_dec_lt(v_i_3675_, v___x_3677_);
                if v___x_3678_ == 0 {
                    lean_dec(v_i_3675_);
                    return v_entries_3676_;
                } else {
                    v_k_3679_ = lean_array_fget_borrowed(v_keys_3673_, v_i_3675_);
                    v_v_3680_ = lean_array_fget_borrowed(v_vals_3674_, v_i_3675_);
                    v___x_3681_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_3679_);
                    v_h_3682_ = lean_uint64_to_usize(v___x_3681_);
                    v___x_3683_ = 5usize;
                    v___x_3684_ = lean_unsigned_to_nat(1);
                    v___x_3685_ = 1usize;
                    v___x_3686_ = lean_usize_sub(v_depth_3672_, v___x_3685_);
                    v___x_3687_ = lean_usize_mul(v___x_3683_, v___x_3686_);
                    v_h_3688_ = lean_usize_shift_right(v_h_3682_, v___x_3687_);
                    v___x_3689_ = lean_nat_add(v_i_3675_, v___x_3684_);
                    lean_dec(v_i_3675_);
                    lean_inc(v_v_3680_);
                    lean_inc(v_k_3679_);
                    v___x_3690_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_entries_3676_, v_h_3688_, v_depth_3672_, v_k_3679_, v_v_3680_);
                    v_i_3675_ = v___x_3689_;
                    v_entries_3676_ = v___x_3690_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_3692_: *mut LeanObject,
    mut v_keys_3693_: *mut LeanObject,
    mut v_vals_3694_: *mut LeanObject,
    mut v_i_3695_: *mut LeanObject,
    mut v_entries_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3697_: usize = 0;
    let mut v_res_3698_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3697_ = lean_unbox_usize(v_depth_3692_);
    lean_dec(v_depth_3692_);
    v_res_3698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_3697_, v_keys_3693_, v_vals_3694_, v_i_3695_, v_entries_3696_);
    lean_dec_ref(v_vals_3694_);
    lean_dec_ref(v_keys_3693_);
    return v_res_3698_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(
    mut v_x_3699_: *mut LeanObject,
    mut v_x_3700_: *mut LeanObject,
    mut v_x_3701_: *mut LeanObject,
    mut v_x_3702_: *mut LeanObject,
    mut v_x_3703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_398__boxed_3704_: usize = 0;
    let mut v_x_399__boxed_3705_: usize = 0;
    let mut v_res_3706_: *mut LeanObject = core::ptr::null_mut();
    v_x_398__boxed_3704_ = lean_unbox_usize(v_x_3700_);
    lean_dec(v_x_3700_);
    v_x_399__boxed_3705_ = lean_unbox_usize(v_x_3701_);
    lean_dec(v_x_3701_);
    v_res_3706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_3699_, v_x_398__boxed_3704_, v_x_399__boxed_3705_, v_x_3702_, v_x_3703_);
    return v_res_3706_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(
    mut v_x_3707_: *mut LeanObject,
    mut v_x_3708_: *mut LeanObject,
    mut v_x_3709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3710_: u64 = 0;
    let mut v___x_3711_: usize = 0;
    let mut v___x_3712_: usize = 0;
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    v___x_3710_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3708_);
    v___x_3711_ = lean_uint64_to_usize(v___x_3710_);
    v___x_3712_ = 1usize;
    v___x_3713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_3707_, v___x_3711_, v___x_3712_, v_x_3708_, v_x_3709_);
    return v___x_3713_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(
    mut v_m_3714_: *mut LeanObject,
    mut v_e_3715_: *mut LeanObject,
    mut v_opId_3716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    v___x_3717_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
            v_m_3714_, v_e_3715_,
        );
    if lean_obj_tag(v___x_3717_) == 1 {
        let mut v_val_3718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
        v_val_3718_ = lean_ctor_get(v___x_3717_, 0);
        lean_inc(v_val_3718_);
        lean_dec_ref_known(v___x_3717_, 1);
        v___x_3719_ =
            l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(
                v_opId_3716_,
                v_val_3718_,
            );
        v___x_3720_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_3714_, v_e_3715_, v___x_3719_);
        return v___x_3720_;
    } else {
        let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3717_);
        v___x_3721_ = lean_box(0);
        v___x_3722_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3722_, 0, v_opId_3716_);
        lean_ctor_set(v___x_3722_, 1, v___x_3721_);
        v___x_3723_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_3714_, v_e_3715_, v___x_3722_);
        return v___x_3723_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(
    mut v_00_u03b2_3724_: *mut LeanObject,
    mut v_x_3725_: *mut LeanObject,
    mut v_x_3726_: *mut LeanObject,
    mut v_x_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    v___x_3728_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_x_3725_, v_x_3726_, v_x_3727_);
    return v___x_3728_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(
    mut v_00_u03b2_3729_: *mut LeanObject,
    mut v_x_3730_: *mut LeanObject,
    mut v_x_3731_: usize,
    mut v_x_3732_: usize,
    mut v_x_3733_: *mut LeanObject,
    mut v_x_3734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_3730_, v_x_3731_, v_x_3732_, v_x_3733_, v_x_3734_);
    return v___x_3735_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(
    mut v_00_u03b2_3736_: *mut LeanObject,
    mut v_x_3737_: *mut LeanObject,
    mut v_x_3738_: *mut LeanObject,
    mut v_x_3739_: *mut LeanObject,
    mut v_x_3740_: *mut LeanObject,
    mut v_x_3741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_590__boxed_3742_: usize = 0;
    let mut v_x_591__boxed_3743_: usize = 0;
    let mut v_res_3744_: *mut LeanObject = core::ptr::null_mut();
    v_x_590__boxed_3742_ = lean_unbox_usize(v_x_3738_);
    lean_dec(v_x_3738_);
    v_x_591__boxed_3743_ = lean_unbox_usize(v_x_3739_);
    lean_dec(v_x_3739_);
    v_res_3744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(v_00_u03b2_3736_, v_x_3737_, v_x_590__boxed_3742_, v_x_591__boxed_3743_, v_x_3740_, v_x_3741_);
    return v_res_3744_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3745_: *mut LeanObject,
    mut v_n_3746_: *mut LeanObject,
    mut v_k_3747_: *mut LeanObject,
    mut v_v_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_3749_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v_n_3746_, v_k_3747_, v_v_3748_);
    return v___x_3749_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3750_: *mut LeanObject,
    mut v_depth_3751_: usize,
    mut v_keys_3752_: *mut LeanObject,
    mut v_vals_3753_: *mut LeanObject,
    mut v_heq_3754_: *mut LeanObject,
    mut v_i_3755_: *mut LeanObject,
    mut v_entries_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    v___x_3757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_3751_, v_keys_3752_, v_vals_3753_, v_i_3755_, v_entries_3756_);
    return v___x_3757_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3758_: *mut LeanObject,
    mut v_depth_3759_: *mut LeanObject,
    mut v_keys_3760_: *mut LeanObject,
    mut v_vals_3761_: *mut LeanObject,
    mut v_heq_3762_: *mut LeanObject,
    mut v_i_3763_: *mut LeanObject,
    mut v_entries_3764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3765_: usize = 0;
    let mut v_res_3766_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3765_ = lean_unbox_usize(v_depth_3759_);
    lean_dec(v_depth_3759_);
    v_res_3766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(v_00_u03b2_3758_, v_depth_boxed_3765_, v_keys_3760_, v_vals_3761_, v_heq_3762_, v_i_3763_, v_entries_3764_);
    lean_dec_ref(v_vals_3761_);
    lean_dec_ref(v_keys_3760_);
    return v_res_3766_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3767_: *mut LeanObject,
    mut v_x_3768_: *mut LeanObject,
    mut v_x_3769_: *mut LeanObject,
    mut v_x_3770_: *mut LeanObject,
    mut v_x_3771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    v___x_3772_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3768_, v_x_3769_, v_x_3770_, v_x_3771_);
    return v___x_3772_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(
    mut v_e_3773_: *mut LeanObject,
    mut v_a_3774_: *mut LeanObject,
    mut v_s_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3776_ = lean_ctor_get(v_s_3775_, 0);
                v_opIdOf_3777_ = lean_ctor_get(v_s_3775_, 1);
                v_exprToOpIds_3778_ = lean_ctor_get(v_s_3775_, 2);
                v_steps_3779_ = lean_ctor_get(v_s_3775_, 3);
                v_isSharedCheck_3787_ = (!lean_is_exclusive(v_s_3775_)) as u8;
                if v_isSharedCheck_3787_ == 0 {
                    v___x_3781_ = v_s_3775_;
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_3779_);
                    lean_inc(v_exprToOpIds_3778_);
                    lean_inc(v_opIdOf_3777_);
                    lean_inc(v_structs_3776_);
                    lean_dec(v_s_3775_);
                    v___x_3781_ = lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_3774_);
                v___x_3783_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(
                        v_exprToOpIds_3778_,
                        v_e_3773_,
                        v_a_3774_,
                    );
                if v_isShared_3782_ == 0 {
                    lean_ctor_set(v___x_3781_, 2, v___x_3783_);
                    v___x_3785_ = v___x_3781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_structs_3776_);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_opIdOf_3777_);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 2, v___x_3783_);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_steps_3779_);
                    v___x_3785_ = v_reuseFailAlloc_3786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(
    mut v_e_3788_: *mut LeanObject,
    mut v_a_3789_: *mut LeanObject,
    mut v_s_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3791_: *mut LeanObject = core::ptr::null_mut();
    v_res_3791_ =
        l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(v_e_3788_, v_a_3789_, v_s_3790_);
    lean_dec(v_a_3789_);
    return v_res_3791_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg(
    mut v_e_3792_: *mut LeanObject,
    mut v_a_3793_: *mut LeanObject,
    mut v_a_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_3793_);
    v___f_3796_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3796_, 0, v_e_3792_);
    lean_closure_set(v___f_3796_, 1, v_a_3793_);
    v___x_3797_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_3798_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3797_, v___f_3796_, v_a_3794_);
    return v___x_3798_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(
    mut v_e_3799_: *mut LeanObject,
    mut v_a_3800_: *mut LeanObject,
    mut v_a_3801_: *mut LeanObject,
    mut v_a_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3803_: *mut LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_3799_, v_a_3800_, v_a_3801_);
    lean_dec(v_a_3801_);
    lean_dec(v_a_3800_);
    return v_res_3803_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId(
    mut v_e_3804_: *mut LeanObject,
    mut v_a_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
    mut v_a_3807_: *mut LeanObject,
    mut v_a_3808_: *mut LeanObject,
    mut v_a_3809_: *mut LeanObject,
    mut v_a_3810_: *mut LeanObject,
    mut v_a_3811_: *mut LeanObject,
    mut v_a_3812_: *mut LeanObject,
    mut v_a_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_3804_, v_a_3805_, v_a_3806_);
    return v___x_3817_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___boxed(
    mut v_e_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
    mut v_a_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_a_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
    mut v_a_3825_: *mut LeanObject,
    mut v_a_3826_: *mut LeanObject,
    mut v_a_3827_: *mut LeanObject,
    mut v_a_3828_: *mut LeanObject,
    mut v_a_3829_: *mut LeanObject,
    mut v_a_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3831_: *mut LeanObject = core::ptr::null_mut();
    v_res_3831_ = l_Lean_Meta_Grind_AC_addTermOpId(
        v_e_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_,
        v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_,
    );
    lean_dec(v_a_3829_);
    lean_dec_ref(v_a_3828_);
    lean_dec(v_a_3827_);
    lean_dec_ref(v_a_3826_);
    lean_dec(v_a_3825_);
    lean_dec_ref(v_a_3824_);
    lean_dec(v_a_3823_);
    lean_dec_ref(v_a_3822_);
    lean_dec(v_a_3821_);
    lean_dec(v_a_3820_);
    lean_dec(v_a_3819_);
    return v_res_3831_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_mkVar___lam__0(
    mut v_e_3832_: *mut LeanObject,
    mut v_size_3833_: *mut LeanObject,
    mut v_s_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_op_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assocInst_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commInst_x3f_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neutralInst_x3f_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_3852_: u8 = 0;
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_3835_ = lean_ctor_get(v_s_3834_, 0);
                v_type_3836_ = lean_ctor_get(v_s_3834_, 1);
                v_u_3837_ = lean_ctor_get(v_s_3834_, 2);
                v_op_3838_ = lean_ctor_get(v_s_3834_, 3);
                v_neutral_x3f_3839_ = lean_ctor_get(v_s_3834_, 4);
                v_assocInst_3840_ = lean_ctor_get(v_s_3834_, 5);
                v_idempotentInst_x3f_3841_ = lean_ctor_get(v_s_3834_, 6);
                v_commInst_x3f_3842_ = lean_ctor_get(v_s_3834_, 7);
                v_neutralInst_x3f_3843_ = lean_ctor_get(v_s_3834_, 8);
                v_nextId_3844_ = lean_ctor_get(v_s_3834_, 9);
                v_vars_3845_ = lean_ctor_get(v_s_3834_, 10);
                v_varMap_3846_ = lean_ctor_get(v_s_3834_, 11);
                v_denote_3847_ = lean_ctor_get(v_s_3834_, 12);
                v_denoteEntries_3848_ = lean_ctor_get(v_s_3834_, 13);
                v_queue_3849_ = lean_ctor_get(v_s_3834_, 14);
                v_basis_3850_ = lean_ctor_get(v_s_3834_, 15);
                v_diseqs_3851_ = lean_ctor_get(v_s_3834_, 16);
                v_recheck_3852_ = lean_ctor_get_uint8(
                    v_s_3834_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_isSharedCheck_3861_ = (!lean_is_exclusive(v_s_3834_)) as u8;
                if v_isSharedCheck_3861_ == 0 {
                    v___x_3854_ = v_s_3834_;
                    v_isShared_3855_ = v_isSharedCheck_3861_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diseqs_3851_);
                    lean_inc(v_basis_3850_);
                    lean_inc(v_queue_3849_);
                    lean_inc(v_denoteEntries_3848_);
                    lean_inc(v_denote_3847_);
                    lean_inc(v_varMap_3846_);
                    lean_inc(v_vars_3845_);
                    lean_inc(v_nextId_3844_);
                    lean_inc(v_neutralInst_x3f_3843_);
                    lean_inc(v_commInst_x3f_3842_);
                    lean_inc(v_idempotentInst_x3f_3841_);
                    lean_inc(v_assocInst_3840_);
                    lean_inc(v_neutral_x3f_3839_);
                    lean_inc(v_op_3838_);
                    lean_inc(v_u_3837_);
                    lean_inc(v_type_3836_);
                    lean_inc(v_id_3835_);
                    lean_dec(v_s_3834_);
                    v___x_3854_ = lean_box(0);
                    v_isShared_3855_ = v_isSharedCheck_3861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_e_3832_);
                v___x_3856_ = l_Lean_PersistentArray_push___redArg(v_vars_3845_, v_e_3832_);
                v___x_3857_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_varMap_3846_, v_e_3832_, v_size_3833_);
                if v_isShared_3855_ == 0 {
                    lean_ctor_set(v___x_3854_, 11, v___x_3857_);
                    lean_ctor_set(v___x_3854_, 10, v___x_3856_);
                    v___x_3859_ = v___x_3854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 17, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_id_3835_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_type_3836_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 2, v_u_3837_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 3, v_op_3838_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 4, v_neutral_x3f_3839_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 5, v_assocInst_3840_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 6, v_idempotentInst_x3f_3841_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 7, v_commInst_x3f_3842_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 8, v_neutralInst_x3f_3843_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 9, v_nextId_3844_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 10, v___x_3856_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 11, v___x_3857_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 12, v_denote_3847_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 13, v_denoteEntries_3848_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 14, v_queue_3849_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 15, v_basis_3850_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 16, v_diseqs_3851_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3860_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_3852_,
                    );
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_mkVar(
    mut v_e_3862_: *mut LeanObject,
    mut v_a_3863_: *mut LeanObject,
    mut v_a_3864_: *mut LeanObject,
    mut v_a_3865_: *mut LeanObject,
    mut v_a_3866_: *mut LeanObject,
    mut v_a_3867_: *mut LeanObject,
    mut v_a_3868_: *mut LeanObject,
    mut v_a_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v_vars_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3899_: u8 = 0;
    let mut v_unused_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v_a_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v_a_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
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
                v___x_3875_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_,
                    v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_,
                );
                if lean_obj_tag(v___x_3875_) == 0 {
                    v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
                    v_isSharedCheck_3925_ = (!lean_is_exclusive(v___x_3875_)) as u8;
                    if v_isSharedCheck_3925_ == 0 {
                        v___x_3878_ = v___x_3875_;
                        v_isShared_3879_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3876_);
                        lean_dec(v___x_3875_);
                        v___x_3878_ = lean_box(0);
                        v_isShared_3879_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3862_);
                    v_a_3926_ = lean_ctor_get(v___x_3875_, 0);
                    v_isSharedCheck_3933_ = (!lean_is_exclusive(v___x_3875_)) as u8;
                    if v_isSharedCheck_3933_ == 0 {
                        v___x_3928_ = v___x_3875_;
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3926_);
                        lean_dec(v___x_3875_);
                        v___x_3928_ = lean_box(0);
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_3880_ = lean_ctor_get(v_a_3876_, 10);
                lean_inc_ref(v_vars_3880_);
                v_varMap_3881_ = lean_ctor_get(v_a_3876_, 11);
                lean_inc_ref(v_varMap_3881_);
                lean_dec(v_a_3876_);
                v___x_3882_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_varMap_3881_, v_e_3862_);
                lean_dec_ref(v_varMap_3881_);
                if lean_obj_tag(v___x_3882_) == 1 {
                    lean_dec_ref(v_vars_3880_);
                    lean_dec_ref(v_e_3862_);
                    v_val_3883_ = lean_ctor_get(v___x_3882_, 0);
                    lean_inc(v_val_3883_);
                    lean_dec_ref_known(v___x_3882_, 1);
                    if v_isShared_3879_ == 0 {
                        lean_ctor_set(v___x_3878_, 0, v_val_3883_);
                        v___x_3885_ = v___x_3878_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_val_3883_);
                        v___x_3885_ = v_reuseFailAlloc_3886_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3882_);
                    lean_del_object(v___x_3878_);
                    v_size_3887_ = lean_ctor_get(v_vars_3880_, 2);
                    lean_inc_n(v_size_3887_, 2);
                    lean_dec_ref(v_vars_3880_);
                    lean_inc_ref(v_e_3862_);
                    v___f_3888_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_AC_mkVar___lam__0 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_3888_, 0, v_e_3862_);
                    lean_closure_set(v___f_3888_, 1, v_size_3887_);
                    v___x_3889_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(
                        v___f_3888_,
                        v_a_3863_,
                        v_a_3864_,
                    );
                    if lean_obj_tag(v___x_3889_) == 0 {
                        lean_dec_ref_known(v___x_3889_, 1);
                        lean_inc_ref(v_e_3862_);
                        v___x_3890_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(
                            v_e_3862_, v_a_3863_, v_a_3864_,
                        );
                        if lean_obj_tag(v___x_3890_) == 0 {
                            lean_dec_ref_known(v___x_3890_, 1);
                            v___x_3891_ = l_Lean_Meta_Grind_AC_acExt;
                            v___x_3892_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                                v___x_3891_,
                                v_e_3862_,
                                v_a_3864_,
                                v_a_3865_,
                                v_a_3866_,
                                v_a_3867_,
                                v_a_3868_,
                                v_a_3869_,
                                v_a_3870_,
                                v_a_3871_,
                                v_a_3872_,
                                v_a_3873_,
                            );
                            if lean_obj_tag(v___x_3892_) == 0 {
                                v_isSharedCheck_3899_ = (!lean_is_exclusive(v___x_3892_)) as u8;
                                if v_isSharedCheck_3899_ == 0 {
                                    v_unused_3900_ = lean_ctor_get(v___x_3892_, 0);
                                    lean_dec(v_unused_3900_);
                                    v___x_3894_ = v___x_3892_;
                                    v_isShared_3895_ = v_isSharedCheck_3899_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v___x_3892_);
                                    v___x_3894_ = lean_box(0);
                                    v_isShared_3895_ = v_isSharedCheck_3899_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v_size_3887_);
                                v_a_3901_ = lean_ctor_get(v___x_3892_, 0);
                                v_isSharedCheck_3908_ = (!lean_is_exclusive(v___x_3892_)) as u8;
                                if v_isSharedCheck_3908_ == 0 {
                                    v___x_3903_ = v___x_3892_;
                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_3901_);
                                    lean_dec(v___x_3892_);
                                    v___x_3903_ = lean_box(0);
                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_size_3887_);
                            lean_dec_ref(v_e_3862_);
                            v_a_3909_ = lean_ctor_get(v___x_3890_, 0);
                            v_isSharedCheck_3916_ = (!lean_is_exclusive(v___x_3890_)) as u8;
                            if v_isSharedCheck_3916_ == 0 {
                                v___x_3911_ = v___x_3890_;
                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3909_);
                                lean_dec(v___x_3890_);
                                v___x_3911_ = lean_box(0);
                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_size_3887_);
                        lean_dec_ref(v_e_3862_);
                        v_a_3917_ = lean_ctor_get(v___x_3889_, 0);
                        v_isSharedCheck_3924_ = (!lean_is_exclusive(v___x_3889_)) as u8;
                        if v_isSharedCheck_3924_ == 0 {
                            v___x_3919_ = v___x_3889_;
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3917_);
                            lean_dec(v___x_3889_);
                            v___x_3919_ = lean_box(0);
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3885_;
            }
            3 => {
                if v_isShared_3895_ == 0 {
                    lean_ctor_set(v___x_3894_, 0, v_size_3887_);
                    v___x_3897_ = v___x_3894_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_size_3887_);
                    v___x_3897_ = v_reuseFailAlloc_3898_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3897_;
            }
            5 => {
                if v_isShared_3904_ == 0 {
                    v___x_3906_ = v___x_3903_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
                    v___x_3906_ = v_reuseFailAlloc_3907_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3906_;
            }
            7 => {
                if v_isShared_3912_ == 0 {
                    v___x_3914_ = v___x_3911_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
                    v___x_3914_ = v_reuseFailAlloc_3915_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3914_;
            }
            9 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3922_;
            }
            11 => {
                if v_isShared_3929_ == 0 {
                    v___x_3931_ = v___x_3928_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
                    v___x_3931_ = v_reuseFailAlloc_3932_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_mkVar___boxed(
    mut v_e_3934_: *mut LeanObject,
    mut v_a_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
    mut v_a_3942_: *mut LeanObject,
    mut v_a_3943_: *mut LeanObject,
    mut v_a_3944_: *mut LeanObject,
    mut v_a_3945_: *mut LeanObject,
    mut v_a_3946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3947_: *mut LeanObject = core::ptr::null_mut();
    v_res_3947_ = l_Lean_Meta_Grind_AC_mkVar(
        v_e_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_,
        v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_,
    );
    lean_dec(v_a_3945_);
    lean_dec_ref(v_a_3944_);
    lean_dec(v_a_3943_);
    lean_dec_ref(v_a_3942_);
    lean_dec(v_a_3941_);
    lean_dec_ref(v_a_3940_);
    lean_dec(v_a_3939_);
    lean_dec_ref(v_a_3938_);
    lean_dec(v_a_3937_);
    lean_dec(v_a_3936_);
    lean_dec(v_a_3935_);
    return v_res_3947_;
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(
    mut v_e_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3963_: u8 = 0;
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut v_unused_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3951_ = lean_st_ref_get(v___y_3949_);
                v_mctx_3952_ = lean_ctor_get(v___x_3951_, 0);
                lean_inc_ref(v_mctx_3952_);
                lean_dec(v___x_3951_);
                v___x_3953_ = lean_instantiate_expr_mvars(v_mctx_3952_, v_e_3948_);
                v_fst_3954_ = lean_ctor_get(v___x_3953_, 0);
                lean_inc(v_fst_3954_);
                v_snd_3955_ = lean_ctor_get(v___x_3953_, 1);
                lean_inc(v_snd_3955_);
                lean_dec_ref(v___x_3953_);
                v___x_3956_ = lean_st_ref_take(v___y_3949_);
                v_cache_3957_ = lean_ctor_get(v___x_3956_, 1);
                v_zetaDeltaFVarIds_3958_ = lean_ctor_get(v___x_3956_, 2);
                v_postponed_3959_ = lean_ctor_get(v___x_3956_, 3);
                v_diag_3960_ = lean_ctor_get(v___x_3956_, 4);
                v_isSharedCheck_3969_ = (!lean_is_exclusive(v___x_3956_)) as u8;
                if v_isSharedCheck_3969_ == 0 {
                    v_unused_3970_ = lean_ctor_get(v___x_3956_, 0);
                    lean_dec(v_unused_3970_);
                    v___x_3962_ = v___x_3956_;
                    v_isShared_3963_ = v_isSharedCheck_3969_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3960_);
                    lean_inc(v_postponed_3959_);
                    lean_inc(v_zetaDeltaFVarIds_3958_);
                    lean_inc(v_cache_3957_);
                    lean_dec(v___x_3956_);
                    v___x_3962_ = lean_box(0);
                    v_isShared_3963_ = v_isSharedCheck_3969_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3963_ == 0 {
                    lean_ctor_set(v___x_3962_, 0, v_fst_3954_);
                    v___x_3965_ = v___x_3962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_fst_3954_);
                    lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_cache_3957_);
                    lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_zetaDeltaFVarIds_3958_);
                    lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_postponed_3959_);
                    lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_diag_3960_);
                    v___x_3965_ = v_reuseFailAlloc_3968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3966_ = lean_st_ref_set(v___y_3949_, v___x_3965_);
                v___x_3967_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3967_, 0, v_snd_3955_);
                return v___x_3967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(
    mut v_e_3971_: *mut LeanObject,
    mut v___y_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3974_: *mut LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_3971_, v___y_3972_);
    lean_dec(v___y_3972_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(
    mut v_e_3975_: *mut LeanObject,
    mut v___y_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    v___x_3987_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_3975_, v___y_3983_);
    return v___x_3987_;
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(
    mut v_e_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
    mut v___y_3999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4000_: *mut LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
    lean_dec(v___y_3998_);
    lean_dec_ref(v___y_3997_);
    lean_dec(v___y_3996_);
    lean_dec_ref(v___y_3995_);
    lean_dec(v___y_3994_);
    lean_dec_ref(v___y_3993_);
    lean_dec(v___y_3992_);
    lean_dec_ref(v___y_3991_);
    lean_dec(v___y_3990_);
    lean_dec(v___y_3989_);
    return v_res_4000_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    v___x_4001_ = lean_unsigned_to_nat(32);
    v___x_4002_ = lean_mk_empty_array_with_capacity(v___x_4001_);
    v___x_4003_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4003_, 0, v___x_4002_);
    return v___x_4003_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4004_: usize = 0;
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    v___x_4004_ = 5usize;
    v___x_4005_ = lean_unsigned_to_nat(0);
    v___x_4006_ = lean_unsigned_to_nat(32);
    v___x_4007_ = lean_mk_empty_array_with_capacity(v___x_4006_);
    v___x_4008_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
    v___x_4009_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4009_, 0, v___x_4008_);
    lean_ctor_set(v___x_4009_, 1, v___x_4007_);
    lean_ctor_set(v___x_4009_, 2, v___x_4005_);
    lean_ctor_set(v___x_4009_, 3, v___x_4005_);
    lean_ctor_set_usize(v___x_4009_, 4, v___x_4004_);
    return v___x_4009_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    v___x_4010_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4010_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    v___x_4011_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
    v___x_4012_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4012_, 0, v___x_4011_);
    return v___x_4012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(
    mut v___x_4013_: *mut LeanObject,
    mut v_binderType_4014_: *mut LeanObject,
    mut v_a_4015_: *mut LeanObject,
    mut v_op_4016_: *mut LeanObject,
    mut v_snd_4017_: *mut LeanObject,
    mut v_val_4018_: *mut LeanObject,
    mut v_a_4019_: *mut LeanObject,
    mut v_a_4020_: *mut LeanObject,
    mut v_fst_4021_: *mut LeanObject,
    mut v_a_4022_: u8,
    mut v_s_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4030_: u8 = 0;
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_4024_ = lean_ctor_get(v_s_4023_, 0);
                v_opIdOf_4025_ = lean_ctor_get(v_s_4023_, 1);
                v_exprToOpIds_4026_ = lean_ctor_get(v_s_4023_, 2);
                v_steps_4027_ = lean_ctor_get(v_s_4023_, 3);
                v_isSharedCheck_4041_ = (!lean_is_exclusive(v_s_4023_)) as u8;
                if v_isSharedCheck_4041_ == 0 {
                    v___x_4029_ = v_s_4023_;
                    v_isShared_4030_ = v_isSharedCheck_4041_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_4027_);
                    lean_inc(v_exprToOpIds_4026_);
                    lean_inc(v_opIdOf_4025_);
                    lean_inc(v_structs_4024_);
                    lean_dec(v_s_4023_);
                    v___x_4029_ = lean_box(0);
                    v_isShared_4030_ = v_isSharedCheck_4041_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4031_ = lean_unsigned_to_nat(0);
                v___x_4032_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
                v___x_4033_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
                v___x_4034_ = lean_box(1);
                v___x_4035_ = lean_box(0);
                v___x_4036_ = lean_alloc_ctor(0, 17, (1) as u32);
                lean_ctor_set(v___x_4036_, 0, v___x_4013_);
                lean_ctor_set(v___x_4036_, 1, v_binderType_4014_);
                lean_ctor_set(v___x_4036_, 2, v_a_4015_);
                lean_ctor_set(v___x_4036_, 3, v_op_4016_);
                lean_ctor_set(v___x_4036_, 4, v_snd_4017_);
                lean_ctor_set(v___x_4036_, 5, v_val_4018_);
                lean_ctor_set(v___x_4036_, 6, v_a_4019_);
                lean_ctor_set(v___x_4036_, 7, v_a_4020_);
                lean_ctor_set(v___x_4036_, 8, v_fst_4021_);
                lean_ctor_set(v___x_4036_, 9, v___x_4031_);
                lean_ctor_set(v___x_4036_, 10, v___x_4032_);
                lean_ctor_set(v___x_4036_, 11, v___x_4033_);
                lean_ctor_set(v___x_4036_, 12, v___x_4033_);
                lean_ctor_set(v___x_4036_, 13, v___x_4032_);
                lean_ctor_set(v___x_4036_, 14, v___x_4034_);
                lean_ctor_set(v___x_4036_, 15, v___x_4035_);
                lean_ctor_set(v___x_4036_, 16, v___x_4032_);
                lean_ctor_set_uint8(
                    v___x_4036_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                    v_a_4022_,
                );
                v___x_4037_ = lean_array_push(v_structs_4024_, v___x_4036_);
                if v_isShared_4030_ == 0 {
                    lean_ctor_set(v___x_4029_, 0, v___x_4037_);
                    v___x_4039_ = v___x_4029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_opIdOf_4025_);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_exprToOpIds_4026_);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_steps_4027_);
                    v___x_4039_ = v_reuseFailAlloc_4040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(
    mut v___x_4042_: *mut LeanObject,
    mut v_binderType_4043_: *mut LeanObject,
    mut v_a_4044_: *mut LeanObject,
    mut v_op_4045_: *mut LeanObject,
    mut v_snd_4046_: *mut LeanObject,
    mut v_val_4047_: *mut LeanObject,
    mut v_a_4048_: *mut LeanObject,
    mut v_a_4049_: *mut LeanObject,
    mut v_fst_4050_: *mut LeanObject,
    mut v_a_4051_: *mut LeanObject,
    mut v_s_4052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_158442__boxed_4053_: u8 = 0;
    let mut v_res_4054_: *mut LeanObject = core::ptr::null_mut();
    v_a_158442__boxed_4053_ = (lean_unbox(v_a_4051_) as u8);
    v_res_4054_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(
            v___x_4042_,
            v_binderType_4043_,
            v_a_4044_,
            v_op_4045_,
            v_snd_4046_,
            v_val_4047_,
            v_a_4048_,
            v_a_4049_,
            v_fst_4050_,
            v_a_158442__boxed_4053_,
            v_s_4052_,
        );
    return v_res_4054_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(
    mut v_m_4055_: *mut LeanObject,
    mut v_a_4056_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: u64 = 0;
    let mut v___x_4061_: u64 = 0;
    let mut v___x_4062_: u64 = 0;
    let mut v_fold_4063_: u64 = 0;
    let mut v___x_4064_: u64 = 0;
    let mut v___x_4065_: u64 = 0;
    let mut v___x_4066_: u64 = 0;
    let mut v___x_4067_: usize = 0;
    let mut v___x_4068_: usize = 0;
    let mut v___x_4069_: usize = 0;
    let mut v___x_4070_: usize = 0;
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: u64 = 0;
    let mut v_hash_4075_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4057_ = lean_ctor_get(v_m_4055_, 1);
                v___x_4058_ = lean_array_get_size(v_buckets_4057_);
                if lean_obj_tag(v_a_4056_) == 0 {
                    v___x_4074_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4060_ = v___x_4074_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4075_ = lean_ctor_get_uint64(
                        v_a_4056_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4060_ = v_hash_4075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4061_ = 32u64;
                v___x_4062_ = lean_uint64_shift_right(v___y_4060_, v___x_4061_);
                v_fold_4063_ = lean_uint64_xor(v___y_4060_, v___x_4062_);
                v___x_4064_ = 16u64;
                v___x_4065_ = lean_uint64_shift_right(v_fold_4063_, v___x_4064_);
                v___x_4066_ = lean_uint64_xor(v_fold_4063_, v___x_4065_);
                v___x_4067_ = lean_uint64_to_usize(v___x_4066_);
                v___x_4068_ = lean_usize_of_nat(v___x_4058_);
                v___x_4069_ = 1usize;
                v___x_4070_ = lean_usize_sub(v___x_4068_, v___x_4069_);
                v___x_4071_ = lean_usize_land(v___x_4067_, v___x_4070_);
                v___x_4072_ = lean_array_uget_borrowed(v_buckets_4057_, v___x_4071_);
                v___x_4073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_4056_, v___x_4072_);
                return v___x_4073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(
    mut v_m_4076_: *mut LeanObject,
    mut v_a_4077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4078_: u8 = 0;
    let mut v_r_4079_: *mut LeanObject = core::ptr::null_mut();
    v_res_4078_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_4076_, v_a_4077_);
    lean_dec(v_a_4077_);
    lean_dec_ref(v_m_4076_);
    v_r_4079_ = lean_box((v_res_4078_) as usize);
    return v_r_4079_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: f64 = 0.0;
    v___x_4080_ = lean_unsigned_to_nat(0);
    v___x_4081_ = lean_float_of_nat(v___x_4080_);
    return v___x_4081_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(
    mut v_cls_4085_: *mut LeanObject,
    mut v_msg_4086_: *mut LeanObject,
    mut v___y_4087_: *mut LeanObject,
    mut v___y_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4097_: u8 = 0;
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4110_: u8 = 0;
    let mut v_tid_4111_: u64 = 0;
    let mut v_traces_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4115_: u8 = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: f64 = 0.0;
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4136_: u8 = 0;
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4092_ = lean_ctor_get(v___y_4089_, 5);
                v___x_4093_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
                v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
                v_isSharedCheck_4138_ = (!lean_is_exclusive(v___x_4093_)) as u8;
                if v_isSharedCheck_4138_ == 0 {
                    v___x_4096_ = v___x_4093_;
                    v_isShared_4097_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4094_);
                    lean_dec(v___x_4093_);
                    v___x_4096_ = lean_box(0);
                    v_isShared_4097_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4098_ = lean_st_ref_take(v___y_4090_);
                v_traceState_4099_ = lean_ctor_get(v___x_4098_, 4);
                v_env_4100_ = lean_ctor_get(v___x_4098_, 0);
                v_nextMacroScope_4101_ = lean_ctor_get(v___x_4098_, 1);
                v_ngen_4102_ = lean_ctor_get(v___x_4098_, 2);
                v_auxDeclNGen_4103_ = lean_ctor_get(v___x_4098_, 3);
                v_cache_4104_ = lean_ctor_get(v___x_4098_, 5);
                v_messages_4105_ = lean_ctor_get(v___x_4098_, 6);
                v_infoState_4106_ = lean_ctor_get(v___x_4098_, 7);
                v_snapshotTasks_4107_ = lean_ctor_get(v___x_4098_, 8);
                v_isSharedCheck_4137_ = (!lean_is_exclusive(v___x_4098_)) as u8;
                if v_isSharedCheck_4137_ == 0 {
                    v___x_4109_ = v___x_4098_;
                    v_isShared_4110_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4107_);
                    lean_inc(v_infoState_4106_);
                    lean_inc(v_messages_4105_);
                    lean_inc(v_cache_4104_);
                    lean_inc(v_traceState_4099_);
                    lean_inc(v_auxDeclNGen_4103_);
                    lean_inc(v_ngen_4102_);
                    lean_inc(v_nextMacroScope_4101_);
                    lean_inc(v_env_4100_);
                    lean_dec(v___x_4098_);
                    v___x_4109_ = lean_box(0);
                    v_isShared_4110_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4111_ = lean_ctor_get_uint64(
                    v_traceState_4099_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4112_ = lean_ctor_get(v_traceState_4099_, 0);
                v_isSharedCheck_4136_ = (!lean_is_exclusive(v_traceState_4099_)) as u8;
                if v_isSharedCheck_4136_ == 0 {
                    v___x_4114_ = v_traceState_4099_;
                    v_isShared_4115_ = v_isSharedCheck_4136_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4112_);
                    lean_dec(v_traceState_4099_);
                    v___x_4114_ = lean_box(0);
                    v_isShared_4115_ = v_isSharedCheck_4136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4116_ = lean_box(0);
                v___x_4117_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0);
                v___x_4118_ = 0;
                v___x_4119_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1;
                v___x_4120_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4120_, 0, v_cls_4085_);
                lean_ctor_set(v___x_4120_, 1, v___x_4116_);
                lean_ctor_set(v___x_4120_, 2, v___x_4119_);
                lean_ctor_set_float(
                    v___x_4120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4117_,
                );
                lean_ctor_set_float(
                    v___x_4120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4117_,
                );
                lean_ctor_set_uint8(
                    v___x_4120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4118_,
                );
                v___x_4121_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2;
                v___x_4122_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4122_, 0, v___x_4120_);
                lean_ctor_set(v___x_4122_, 1, v_a_4094_);
                lean_ctor_set(v___x_4122_, 2, v___x_4121_);
                lean_inc(v_ref_4092_);
                v___x_4123_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4123_, 0, v_ref_4092_);
                lean_ctor_set(v___x_4123_, 1, v___x_4122_);
                v___x_4124_ = l_Lean_PersistentArray_push___redArg(v_traces_4112_, v___x_4123_);
                if v_isShared_4115_ == 0 {
                    lean_ctor_set(v___x_4114_, 0, v___x_4124_);
                    v___x_4126_ = v___x_4114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4124_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4135_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4111_,
                    );
                    v___x_4126_ = v_reuseFailAlloc_4135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4110_ == 0 {
                    lean_ctor_set(v___x_4109_, 4, v___x_4126_);
                    v___x_4128_ = v___x_4109_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_env_4100_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_nextMacroScope_4101_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_ngen_4102_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_auxDeclNGen_4103_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 4, v___x_4126_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 5, v_cache_4104_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 6, v_messages_4105_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 7, v_infoState_4106_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 8, v_snapshotTasks_4107_);
                    v___x_4128_ = v_reuseFailAlloc_4134_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4129_ = lean_st_ref_set(v___y_4090_, v___x_4128_);
                v___x_4130_ = lean_box(0);
                if v_isShared_4097_ == 0 {
                    lean_ctor_set(v___x_4096_, 0, v___x_4130_);
                    v___x_4132_ = v___x_4096_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
                    v___x_4132_ = v_reuseFailAlloc_4133_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(
    mut v_cls_4139_: *mut LeanObject,
    mut v_msg_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4146_: *mut LeanObject = core::ptr::null_mut();
    v_res_4146_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_4139_, v_msg_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
    lean_dec(v___y_4144_);
    lean_dec_ref(v___y_4143_);
    lean_dec(v___y_4142_);
    lean_dec_ref(v___y_4141_);
    return v_res_4146_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1()
-> *mut LeanObject {
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    v___x_4148_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0;
    v___x_4149_ = l_Lean_stringToMessageData(v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4()
-> *mut LeanObject {
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    v___x_4153_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3;
    v___x_4154_ = l_Lean_MessageData_ofFormat(v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6()
-> *mut LeanObject {
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    v___x_4156_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16()
-> *mut LeanObject {
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v___x_4172_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13;
    v___x_4173_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15;
    v___x_4174_ = l_Lean_Name_append(v___x_4173_, v___x_4172_);
    return v___x_4174_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18()
-> *mut LeanObject {
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    v___x_4176_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17;
    v___x_4177_ = l_Lean_stringToMessageData(v___x_4176_);
    return v___x_4177_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(
    mut v_op_4195_: *mut LeanObject,
    mut v_a_4196_: *mut LeanObject,
    mut v_a_4197_: *mut LeanObject,
    mut v_a_4198_: *mut LeanObject,
    mut v_a_4199_: *mut LeanObject,
    mut v_a_4200_: *mut LeanObject,
    mut v_a_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
    mut v_a_4205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v___y_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut v___y_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: u8 = 0;
    let mut v___y_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structs_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4338_: u8 = 0;
    let mut v_inheritedTraceOptions_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: u8 = 0;
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_a_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4363_: u8 = 0;
    let mut v_f_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v_binderType_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4390_: u8 = 0;
    let mut v_binderType_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4408_: u8 = 0;
    let mut v___x_4409_: u8 = 0;
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4419_: u8 = 0;
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v_val_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4435_: u8 = 0;
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: u8 = 0;
    let mut v_reuseFailAlloc_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4475_: u8 = 0;
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_a_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_a_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v_a_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut v_a_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_reuseFailAlloc_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_a_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v_a_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut v_a_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4553_: u8 = 0;
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_a_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4566_: u8 = 0;
    let mut v_isSharedCheck_4567_: u8 = 0;
    let mut v_a_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut v_a_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4597_: u8 = 0;
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4601_: u8 = 0;
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut v_a_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_declName_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_f_4364_ = l_Lean_Expr_getAppFn(v_op_4195_);
                if lean_obj_tag(v_f_4364_) == 4 {
                    v_declName_4627_ = lean_ctor_get(v_f_4364_, 0);
                    lean_inc(v_declName_4627_);
                    v___x_4628_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
                    v___x_4629_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v___x_4628_, v_declName_4627_);
                    lean_dec(v_declName_4627_);
                    if v___x_4629_ == 0 {
                        v___y_4366_ = v_a_4196_;
                        v___y_4367_ = v_a_4197_;
                        v___y_4368_ = v_a_4198_;
                        v___y_4369_ = v_a_4199_;
                        v___y_4370_ = v_a_4200_;
                        v___y_4371_ = v_a_4201_;
                        v___y_4372_ = v_a_4202_;
                        v___y_4373_ = v_a_4203_;
                        v___y_4374_ = v_a_4204_;
                        v___y_4375_ = v_a_4205_;
                        state = 15;
                        continue;
                    } else {
                        lean_dec_ref_known(v_f_4364_, 2);
                        lean_dec_ref(v_op_4195_);
                        v___x_4630_ = lean_box(0);
                        v___x_4631_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4631_, 0, v___x_4630_);
                        return v___x_4631_;
                    }
                } else {
                    v___y_4366_ = v_a_4196_;
                    v___y_4367_ = v_a_4197_;
                    v___y_4368_ = v_a_4198_;
                    v___y_4369_ = v_a_4199_;
                    v___y_4370_ = v_a_4200_;
                    v___y_4371_ = v_a_4201_;
                    v___y_4372_ = v_a_4202_;
                    v___y_4373_ = v_a_4203_;
                    v___y_4374_ = v_a_4204_;
                    v___y_4375_ = v_a_4205_;
                    state = 15;
                    continue;
                }
            }
            1 => {
                v___x_4209_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4209_, 0, v___y_4208_);
                v___x_4210_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4210_, 0, v___x_4209_);
                return v___x_4210_;
            }
            2 => {
                if lean_obj_tag(v___y_4213_) == 1 {
                    v_val_4224_ = lean_ctor_get(v___y_4213_, 0);
                    lean_inc(v_val_4224_);
                    lean_dec_ref_known(v___y_4213_, 1);
                    v___x_4225_ = l_Lean_Meta_Grind_AC_mkVar(
                        v_val_4224_,
                        v___y_4212_,
                        v___y_4214_,
                        v___y_4215_,
                        v___y_4216_,
                        v___y_4217_,
                        v___y_4218_,
                        v___y_4219_,
                        v___y_4220_,
                        v___y_4221_,
                        v___y_4222_,
                        v___y_4223_,
                    );
                    if lean_obj_tag(v___x_4225_) == 0 {
                        lean_dec_ref_known(v___x_4225_, 1);
                        v___y_4208_ = v___y_4212_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___y_4212_);
                        v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
                        v_isSharedCheck_4233_ = (!lean_is_exclusive(v___x_4225_)) as u8;
                        if v_isSharedCheck_4233_ == 0 {
                            v___x_4228_ = v___x_4225_;
                            v_isShared_4229_ = v_isSharedCheck_4233_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4226_);
                            lean_dec(v___x_4225_);
                            v___x_4228_ = lean_box(0);
                            v_isShared_4229_ = v_isSharedCheck_4233_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_4213_);
                    v___y_4208_ = v___y_4212_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4229_ == 0 {
                    v___x_4231_ = v___x_4228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
                    v___x_4231_ = v_reuseFailAlloc_4232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4231_;
            }
            5 => {
                v___x_4250_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4250_, 0, v___y_4246_);
                lean_ctor_set(v___x_4250_, 1, v___y_4249_);
                lean_inc(v___y_4239_);
                v___x_4251_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v___y_4239_, v___x_4250_, v___y_4241_, v___y_4243_, v___y_4248_, v___y_4236_);
                if lean_obj_tag(v___x_4251_) == 0 {
                    lean_dec_ref_known(v___x_4251_, 1);
                    v___y_4212_ = v___y_4237_;
                    v___y_4213_ = v___y_4238_;
                    v___y_4214_ = v___y_4235_;
                    v___y_4215_ = v___y_4242_;
                    v___y_4216_ = v___y_4247_;
                    v___y_4217_ = v___y_4244_;
                    v___y_4218_ = v___y_4240_;
                    v___y_4219_ = v___y_4245_;
                    v___y_4220_ = v___y_4241_;
                    v___y_4221_ = v___y_4243_;
                    v___y_4222_ = v___y_4248_;
                    v___y_4223_ = v___y_4236_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_4238_);
                    lean_dec(v___y_4237_);
                    v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
                    v_isSharedCheck_4259_ = (!lean_is_exclusive(v___x_4251_)) as u8;
                    if v_isSharedCheck_4259_ == 0 {
                        v___x_4254_ = v___x_4251_;
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4252_);
                        lean_dec(v___x_4251_);
                        v___x_4254_ = lean_box(0);
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4255_ == 0 {
                    v___x_4257_ = v___x_4254_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4257_;
            }
            8 => {
                lean_inc_ref(v___y_4275_);
                v___x_4276_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4276_, 0, v___y_4275_);
                v___x_4277_ = l_Lean_MessageData_ofFormat(v___x_4276_);
                v___x_4278_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4278_, 0, v___y_4262_);
                lean_ctor_set(v___x_4278_, 1, v___x_4277_);
                v___x_4279_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
                v___x_4280_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4280_, 0, v___x_4278_);
                lean_ctor_set(v___x_4280_, 1, v___x_4279_);
                if lean_obj_tag(v___y_4265_) == 0 {
                    v___x_4281_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
                    v___y_4235_ = v___y_4261_;
                    v___y_4236_ = v___y_4263_;
                    v___y_4237_ = v___y_4264_;
                    v___y_4238_ = v___y_4265_;
                    v___y_4239_ = v___y_4266_;
                    v___y_4240_ = v___y_4267_;
                    v___y_4241_ = v___y_4268_;
                    v___y_4242_ = v___y_4269_;
                    v___y_4243_ = v___y_4270_;
                    v___y_4244_ = v___y_4271_;
                    v___y_4245_ = v___y_4272_;
                    v___y_4246_ = v___x_4280_;
                    v___y_4247_ = v___y_4273_;
                    v___y_4248_ = v___y_4274_;
                    v___y_4249_ = v___x_4281_;
                    state = 5;
                    continue;
                } else {
                    v_val_4282_ = lean_ctor_get(v___y_4265_, 0);
                    lean_inc(v_val_4282_);
                    v___x_4283_ = l_Lean_MessageData_ofExpr(v_val_4282_);
                    v___y_4235_ = v___y_4261_;
                    v___y_4236_ = v___y_4263_;
                    v___y_4237_ = v___y_4264_;
                    v___y_4238_ = v___y_4265_;
                    v___y_4239_ = v___y_4266_;
                    v___y_4240_ = v___y_4267_;
                    v___y_4241_ = v___y_4268_;
                    v___y_4242_ = v___y_4269_;
                    v___y_4243_ = v___y_4270_;
                    v___y_4244_ = v___y_4271_;
                    v___y_4245_ = v___y_4272_;
                    v___y_4246_ = v___x_4280_;
                    v___y_4247_ = v___y_4273_;
                    v___y_4248_ = v___y_4274_;
                    v___y_4249_ = v___x_4283_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                lean_inc_ref(v___y_4300_);
                v___x_4301_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4301_, 0, v___y_4300_);
                v___x_4302_ = l_Lean_MessageData_ofFormat(v___x_4301_);
                v___x_4303_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4303_, 0, v___y_4285_);
                lean_ctor_set(v___x_4303_, 1, v___x_4302_);
                v___x_4304_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
                v___x_4305_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4305_, 0, v___x_4303_);
                lean_ctor_set(v___x_4305_, 1, v___x_4304_);
                if lean_obj_tag(v___y_4288_) == 0 {
                    v___x_4306_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7;
                    v___y_4261_ = v___y_4286_;
                    v___y_4262_ = v___x_4305_;
                    v___y_4263_ = v___y_4287_;
                    v___y_4264_ = v___y_4289_;
                    v___y_4265_ = v___y_4290_;
                    v___y_4266_ = v___y_4291_;
                    v___y_4267_ = v___y_4292_;
                    v___y_4268_ = v___y_4293_;
                    v___y_4269_ = v___y_4294_;
                    v___y_4270_ = v___y_4295_;
                    v___y_4271_ = v___y_4296_;
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4298_;
                    v___y_4274_ = v___y_4299_;
                    v___y_4275_ = v___x_4306_;
                    state = 8;
                    continue;
                } else {
                    lean_dec_ref_known(v___y_4288_, 1);
                    v___x_4307_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8;
                    v___y_4261_ = v___y_4286_;
                    v___y_4262_ = v___x_4305_;
                    v___y_4263_ = v___y_4287_;
                    v___y_4264_ = v___y_4289_;
                    v___y_4265_ = v___y_4290_;
                    v___y_4266_ = v___y_4291_;
                    v___y_4267_ = v___y_4292_;
                    v___y_4268_ = v___y_4293_;
                    v___y_4269_ = v___y_4294_;
                    v___y_4270_ = v___y_4295_;
                    v___y_4271_ = v___y_4296_;
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4298_;
                    v___y_4274_ = v___y_4299_;
                    v___y_4275_ = v___x_4307_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_4329_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v___y_4319_, v___y_4327_);
                if lean_obj_tag(v___x_4329_) == 0 {
                    v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
                    lean_inc(v_a_4330_);
                    lean_dec_ref_known(v___x_4329_, 1);
                    v_structs_4331_ = lean_ctor_get(v_a_4330_, 0);
                    lean_inc_ref(v_structs_4331_);
                    lean_dec(v_a_4330_);
                    v___x_4332_ = lean_array_get_size(v_structs_4331_);
                    lean_dec_ref(v_structs_4331_);
                    v___x_4333_ = lean_box((v___y_4310_) as usize);
                    lean_inc(v_snd_4318_);
                    lean_inc_ref(v_op_4195_);
                    v___f_4334_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed as *mut core::ffi::c_void, 11, 10);
                    lean_closure_set(v___f_4334_, 0, v___x_4332_);
                    lean_closure_set(v___f_4334_, 1, v___y_4311_);
                    lean_closure_set(v___f_4334_, 2, v___y_4314_);
                    lean_closure_set(v___f_4334_, 3, v_op_4195_);
                    lean_closure_set(v___f_4334_, 4, v_snd_4318_);
                    lean_closure_set(v___f_4334_, 5, v___y_4309_);
                    lean_closure_set(v___f_4334_, 6, v___y_4312_);
                    lean_closure_set(v___f_4334_, 7, v___y_4313_);
                    lean_closure_set(v___f_4334_, 8, v_fst_4317_);
                    lean_closure_set(v___f_4334_, 9, v___x_4333_);
                    v___x_4335_ = l_Lean_Meta_Grind_AC_acExt;
                    v___x_4336_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4335_, v___f_4334_, v___y_4319_);
                    if lean_obj_tag(v___x_4336_) == 0 {
                        lean_dec_ref_known(v___x_4336_, 1);
                        v_options_4337_ = lean_ctor_get(v___y_4327_, 2);
                        v_hasTrace_4338_ = lean_ctor_get_uint8(
                            v_options_4337_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4338_ == 0 {
                            lean_dec(v___y_4316_);
                            lean_dec(v___y_4315_);
                            lean_dec_ref(v_op_4195_);
                            v___y_4212_ = v___x_4332_;
                            v___y_4213_ = v_snd_4318_;
                            v___y_4214_ = v___y_4319_;
                            v___y_4215_ = v___y_4320_;
                            v___y_4216_ = v___y_4321_;
                            v___y_4217_ = v___y_4322_;
                            v___y_4218_ = v___y_4323_;
                            v___y_4219_ = v___y_4324_;
                            v___y_4220_ = v___y_4325_;
                            v___y_4221_ = v___y_4326_;
                            v___y_4222_ = v___y_4327_;
                            v___y_4223_ = v___y_4328_;
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_4339_ = lean_ctor_get(v___y_4327_, 13);
                            v___x_4340_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13;
                            v___x_4341_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16);
                            v___x_4342_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4339_,
                                v_options_4337_,
                                v___x_4341_,
                            );
                            if v___x_4342_ == 0 {
                                lean_dec(v___y_4316_);
                                lean_dec(v___y_4315_);
                                lean_dec_ref(v_op_4195_);
                                v___y_4212_ = v___x_4332_;
                                v___y_4213_ = v_snd_4318_;
                                v___y_4214_ = v___y_4319_;
                                v___y_4215_ = v___y_4320_;
                                v___y_4216_ = v___y_4321_;
                                v___y_4217_ = v___y_4322_;
                                v___y_4218_ = v___y_4323_;
                                v___y_4219_ = v___y_4324_;
                                v___y_4220_ = v___y_4325_;
                                v___y_4221_ = v___y_4326_;
                                v___y_4222_ = v___y_4327_;
                                v___y_4223_ = v___y_4328_;
                                state = 2;
                                continue;
                            } else {
                                v___x_4343_ = l_Lean_MessageData_ofExpr(v_op_4195_);
                                v___x_4344_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18);
                                v___x_4345_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4345_, 0, v___x_4343_);
                                lean_ctor_set(v___x_4345_, 1, v___x_4344_);
                                if lean_obj_tag(v___y_4316_) == 0 {
                                    v___x_4346_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7;
                                    v___y_4285_ = v___x_4345_;
                                    v___y_4286_ = v___y_4319_;
                                    v___y_4287_ = v___y_4328_;
                                    v___y_4288_ = v___y_4315_;
                                    v___y_4289_ = v___x_4332_;
                                    v___y_4290_ = v_snd_4318_;
                                    v___y_4291_ = v___x_4340_;
                                    v___y_4292_ = v___y_4323_;
                                    v___y_4293_ = v___y_4325_;
                                    v___y_4294_ = v___y_4320_;
                                    v___y_4295_ = v___y_4326_;
                                    v___y_4296_ = v___y_4322_;
                                    v___y_4297_ = v___y_4324_;
                                    v___y_4298_ = v___y_4321_;
                                    v___y_4299_ = v___y_4327_;
                                    v___y_4300_ = v___x_4346_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v___y_4316_, 1);
                                    v___x_4347_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8;
                                    v___y_4285_ = v___x_4345_;
                                    v___y_4286_ = v___y_4319_;
                                    v___y_4287_ = v___y_4328_;
                                    v___y_4288_ = v___y_4315_;
                                    v___y_4289_ = v___x_4332_;
                                    v___y_4290_ = v_snd_4318_;
                                    v___y_4291_ = v___x_4340_;
                                    v___y_4292_ = v___y_4323_;
                                    v___y_4293_ = v___y_4325_;
                                    v___y_4294_ = v___y_4320_;
                                    v___y_4295_ = v___y_4326_;
                                    v___y_4296_ = v___y_4322_;
                                    v___y_4297_ = v___y_4324_;
                                    v___y_4298_ = v___y_4321_;
                                    v___y_4299_ = v___y_4327_;
                                    v___y_4300_ = v___x_4347_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_snd_4318_);
                        lean_dec(v___y_4316_);
                        lean_dec(v___y_4315_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4348_ = lean_ctor_get(v___x_4336_, 0);
                        v_isSharedCheck_4355_ = (!lean_is_exclusive(v___x_4336_)) as u8;
                        if v_isSharedCheck_4355_ == 0 {
                            v___x_4350_ = v___x_4336_;
                            v_isShared_4351_ = v_isSharedCheck_4355_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4348_);
                            lean_dec(v___x_4336_);
                            v___x_4350_ = lean_box(0);
                            v_isShared_4351_ = v_isSharedCheck_4355_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_4318_);
                    lean_dec(v_fst_4317_);
                    lean_dec(v___y_4316_);
                    lean_dec(v___y_4315_);
                    lean_dec(v___y_4314_);
                    lean_dec(v___y_4313_);
                    lean_dec(v___y_4312_);
                    lean_dec_ref(v___y_4311_);
                    lean_dec_ref(v___y_4309_);
                    lean_dec_ref(v_op_4195_);
                    v_a_4356_ = lean_ctor_get(v___x_4329_, 0);
                    v_isSharedCheck_4363_ = (!lean_is_exclusive(v___x_4329_)) as u8;
                    if v_isSharedCheck_4363_ == 0 {
                        v___x_4358_ = v___x_4329_;
                        v_isShared_4359_ = v_isSharedCheck_4363_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4356_);
                        lean_dec(v___x_4329_);
                        v___x_4358_ = lean_box(0);
                        v_isShared_4359_ = v_isSharedCheck_4363_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4351_ == 0 {
                    v___x_4353_ = v___x_4350_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4353_;
            }
            13 => {
                if v_isShared_4359_ == 0 {
                    v___x_4361_ = v___x_4358_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
                    v___x_4361_ = v_reuseFailAlloc_4362_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4361_;
            }
            15 => {
                lean_inc(v___y_4375_);
                lean_inc_ref(v___y_4374_);
                lean_inc(v___y_4373_);
                lean_inc_ref(v___y_4372_);
                lean_inc_ref(v_op_4195_);
                v___x_4376_ = lean_infer_type(
                    v_op_4195_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if lean_obj_tag(v___x_4376_) == 0 {
                    v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
                    lean_inc(v_a_4377_);
                    lean_dec_ref_known(v___x_4376_, 1);
                    lean_inc(v___y_4375_);
                    lean_inc_ref(v___y_4374_);
                    lean_inc(v___y_4373_);
                    lean_inc_ref(v___y_4372_);
                    v___x_4378_ = lean_whnf(
                        v_a_4377_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if lean_obj_tag(v___x_4378_) == 0 {
                        v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
                        v_isSharedCheck_4610_ = (!lean_is_exclusive(v___x_4378_)) as u8;
                        if v_isSharedCheck_4610_ == 0 {
                            v___x_4381_ = v___x_4378_;
                            v_isShared_4382_ = v_isSharedCheck_4610_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_4379_);
                            lean_dec(v___x_4378_);
                            v___x_4381_ = lean_box(0);
                            v_isShared_4382_ = v_isSharedCheck_4610_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_f_4364_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4611_ = lean_ctor_get(v___x_4378_, 0);
                        v_isSharedCheck_4618_ = (!lean_is_exclusive(v___x_4378_)) as u8;
                        if v_isSharedCheck_4618_ == 0 {
                            v___x_4613_ = v___x_4378_;
                            v_isShared_4614_ = v_isSharedCheck_4618_;
                            state = 60;
                            continue;
                        } else {
                            lean_inc(v_a_4611_);
                            lean_dec(v___x_4378_);
                            v___x_4613_ = lean_box(0);
                            v_isShared_4614_ = v_isSharedCheck_4618_;
                            state = 60;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_4364_);
                    lean_dec_ref(v_op_4195_);
                    v_a_4619_ = lean_ctor_get(v___x_4376_, 0);
                    v_isSharedCheck_4626_ = (!lean_is_exclusive(v___x_4376_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4376_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 62;
                        continue;
                    } else {
                        lean_inc(v_a_4619_);
                        lean_dec(v___x_4376_);
                        v___x_4621_ = lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 62;
                        continue;
                    }
                }
            }
            16 => {
                if lean_obj_tag(v_a_4379_) == 7 {
                    v_binderType_4383_ = lean_ctor_get(v_a_4379_, 1);
                    lean_inc_ref(v_binderType_4383_);
                    v_body_4384_ = lean_ctor_get(v_a_4379_, 2);
                    lean_inc_ref(v_body_4384_);
                    lean_dec_ref_known(v_a_4379_, 3);
                    v___x_4385_ = l_Lean_Expr_hasLooseBVars(v_body_4384_);
                    if v___x_4385_ == 0 {
                        lean_del_object(v___x_4381_);
                        lean_inc(v___y_4375_);
                        lean_inc_ref(v___y_4374_);
                        lean_inc(v___y_4373_);
                        lean_inc_ref(v___y_4372_);
                        v___x_4386_ = lean_whnf(
                            v_body_4384_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if lean_obj_tag(v___x_4386_) == 0 {
                            v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
                            v_isSharedCheck_4593_ = (!lean_is_exclusive(v___x_4386_)) as u8;
                            if v_isSharedCheck_4593_ == 0 {
                                v___x_4389_ = v___x_4386_;
                                v_isShared_4390_ = v_isSharedCheck_4593_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_4387_);
                                lean_dec(v___x_4386_);
                                v___x_4389_ = lean_box(0);
                                v_isShared_4390_ = v_isSharedCheck_4593_;
                                state = 17;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_binderType_4383_);
                            lean_dec_ref(v_f_4364_);
                            lean_dec_ref(v_op_4195_);
                            v_a_4594_ = lean_ctor_get(v___x_4386_, 0);
                            v_isSharedCheck_4601_ = (!lean_is_exclusive(v___x_4386_)) as u8;
                            if v_isSharedCheck_4601_ == 0 {
                                v___x_4596_ = v___x_4386_;
                                v_isShared_4597_ = v_isSharedCheck_4601_;
                                state = 56;
                                continue;
                            } else {
                                lean_inc(v_a_4594_);
                                lean_dec(v___x_4386_);
                                v___x_4596_ = lean_box(0);
                                v_isShared_4597_ = v_isSharedCheck_4601_;
                                state = 56;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_body_4384_);
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_f_4364_);
                        lean_dec_ref(v_op_4195_);
                        v___x_4602_ = lean_box(0);
                        if v_isShared_4382_ == 0 {
                            lean_ctor_set(v___x_4381_, 0, v___x_4602_);
                            v___x_4604_ = v___x_4381_;
                            state = 58;
                            continue;
                        } else {
                            v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
                            v___x_4604_ = v_reuseFailAlloc_4605_;
                            state = 58;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4379_);
                    lean_dec_ref(v_f_4364_);
                    lean_dec_ref(v_op_4195_);
                    v___x_4606_ = lean_box(0);
                    if v_isShared_4382_ == 0 {
                        lean_ctor_set(v___x_4381_, 0, v___x_4606_);
                        v___x_4608_ = v___x_4381_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
                        v___x_4608_ = v_reuseFailAlloc_4609_;
                        state = 59;
                        continue;
                    }
                }
            }
            17 => {
                if lean_obj_tag(v_a_4387_) == 7 {
                    v_binderType_4391_ = lean_ctor_get(v_a_4387_, 1);
                    lean_inc_ref(v_binderType_4391_);
                    v_body_4392_ = lean_ctor_get(v_a_4387_, 2);
                    lean_inc_ref(v_body_4392_);
                    lean_dec_ref_known(v_a_4387_, 3);
                    v___x_4393_ = l_Lean_Expr_hasLooseBVars(v_body_4392_);
                    if v___x_4393_ == 0 {
                        lean_del_object(v___x_4389_);
                        lean_inc_ref(v_binderType_4383_);
                        v___x_4394_ = l_Lean_Meta_isExprDefEq(
                            v_binderType_4383_,
                            v_binderType_4391_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if lean_obj_tag(v___x_4394_) == 0 {
                            v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
                            v_isSharedCheck_4576_ = (!lean_is_exclusive(v___x_4394_)) as u8;
                            if v_isSharedCheck_4576_ == 0 {
                                v___x_4397_ = v___x_4394_;
                                v_isShared_4398_ = v_isSharedCheck_4576_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4395_);
                                lean_dec(v___x_4394_);
                                v___x_4397_ = lean_box(0);
                                v_isShared_4398_ = v_isSharedCheck_4576_;
                                state = 18;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_body_4392_);
                            lean_dec_ref(v_binderType_4383_);
                            lean_dec_ref(v_f_4364_);
                            lean_dec_ref(v_op_4195_);
                            v_a_4577_ = lean_ctor_get(v___x_4394_, 0);
                            v_isSharedCheck_4584_ = (!lean_is_exclusive(v___x_4394_)) as u8;
                            if v_isSharedCheck_4584_ == 0 {
                                v___x_4579_ = v___x_4394_;
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 52;
                                continue;
                            } else {
                                lean_inc(v_a_4577_);
                                lean_dec(v___x_4394_);
                                v___x_4579_ = lean_box(0);
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 52;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_body_4392_);
                        lean_dec_ref(v_binderType_4391_);
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_f_4364_);
                        lean_dec_ref(v_op_4195_);
                        v___x_4585_ = lean_box(0);
                        if v_isShared_4390_ == 0 {
                            lean_ctor_set(v___x_4389_, 0, v___x_4585_);
                            v___x_4587_ = v___x_4389_;
                            state = 54;
                            continue;
                        } else {
                            v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4585_);
                            v___x_4587_ = v_reuseFailAlloc_4588_;
                            state = 54;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4387_);
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_f_4364_);
                    lean_dec_ref(v_op_4195_);
                    v___x_4589_ = lean_box(0);
                    if v_isShared_4390_ == 0 {
                        lean_ctor_set(v___x_4389_, 0, v___x_4589_);
                        v___x_4591_ = v___x_4389_;
                        state = 55;
                        continue;
                    } else {
                        v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
                        v___x_4591_ = v_reuseFailAlloc_4592_;
                        state = 55;
                        continue;
                    }
                }
            }
            18 => {
                v___x_4399_ = (lean_unbox(v_a_4395_) as u8);
                lean_dec(v_a_4395_);
                if v___x_4399_ == 0 {
                    lean_dec_ref(v_body_4392_);
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_f_4364_);
                    lean_dec_ref(v_op_4195_);
                    v___x_4400_ = lean_box(0);
                    if v_isShared_4398_ == 0 {
                        lean_ctor_set(v___x_4397_, 0, v___x_4400_);
                        v___x_4402_ = v___x_4397_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
                        v___x_4402_ = v_reuseFailAlloc_4403_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4397_);
                    lean_inc_ref(v_binderType_4383_);
                    v___x_4404_ = l_Lean_Meta_isExprDefEq(
                        v_binderType_4383_,
                        v_body_4392_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if lean_obj_tag(v___x_4404_) == 0 {
                        v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
                        v_isSharedCheck_4567_ = (!lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4567_ == 0 {
                            v___x_4407_ = v___x_4404_;
                            v_isShared_4408_ = v_isSharedCheck_4567_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_4405_);
                            lean_dec(v___x_4404_);
                            v___x_4407_ = lean_box(0);
                            v_isShared_4408_ = v_isSharedCheck_4567_;
                            state = 20;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_f_4364_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4568_ = lean_ctor_get(v___x_4404_, 0);
                        v_isSharedCheck_4575_ = (!lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4575_ == 0 {
                            v___x_4570_ = v___x_4404_;
                            v_isShared_4571_ = v_isSharedCheck_4575_;
                            state = 50;
                            continue;
                        } else {
                            lean_inc(v_a_4568_);
                            lean_dec(v___x_4404_);
                            v___x_4570_ = lean_box(0);
                            v_isShared_4571_ = v_isSharedCheck_4575_;
                            state = 50;
                            continue;
                        }
                    }
                }
            }
            19 => {
                return v___x_4402_;
            }
            20 => {
                v___x_4409_ = (lean_unbox(v_a_4405_) as u8);
                lean_dec(v_a_4405_);
                if v___x_4409_ == 0 {
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_f_4364_);
                    lean_dec_ref(v_op_4195_);
                    v___x_4410_ = lean_box(0);
                    if v_isShared_4408_ == 0 {
                        lean_ctor_set(v___x_4407_, 0, v___x_4410_);
                        v___x_4412_ = v___x_4407_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4410_);
                        v___x_4412_ = v_reuseFailAlloc_4413_;
                        state = 21;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4407_);
                    v___x_4414_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_4195_, v_f_4364_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
                    lean_dec_ref(v_f_4364_);
                    if lean_obj_tag(v___x_4414_) == 0 {
                        v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
                        v_isSharedCheck_4558_ = (!lean_is_exclusive(v___x_4414_)) as u8;
                        if v_isSharedCheck_4558_ == 0 {
                            v___x_4417_ = v___x_4414_;
                            v_isShared_4418_ = v_isSharedCheck_4558_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_4415_);
                            lean_dec(v___x_4414_);
                            v___x_4417_ = lean_box(0);
                            v_isShared_4418_ = v_isSharedCheck_4558_;
                            state = 22;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4559_ = lean_ctor_get(v___x_4414_, 0);
                        v_isSharedCheck_4566_ = (!lean_is_exclusive(v___x_4414_)) as u8;
                        if v_isSharedCheck_4566_ == 0 {
                            v___x_4561_ = v___x_4414_;
                            v_isShared_4562_ = v_isSharedCheck_4566_;
                            state = 48;
                            continue;
                        } else {
                            lean_inc(v_a_4559_);
                            lean_dec(v___x_4414_);
                            v___x_4561_ = lean_box(0);
                            v_isShared_4562_ = v_isSharedCheck_4566_;
                            state = 48;
                            continue;
                        }
                    }
                }
            }
            21 => {
                return v___x_4412_;
            }
            22 => {
                v___x_4419_ = (lean_unbox(v_a_4415_) as u8);
                if v___x_4419_ == 0 {
                    lean_del_object(v___x_4417_);
                    lean_inc_ref(v_binderType_4383_);
                    v___x_4420_ = l_Lean_Meta_getLevel(
                        v_binderType_4383_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if lean_obj_tag(v___x_4420_) == 0 {
                        v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
                        lean_inc_n(v_a_4421_, 2);
                        lean_dec_ref_known(v___x_4420_, 1);
                        v___x_4422_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21;
                        v___x_4423_ = lean_box(0);
                        v___x_4424_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4424_, 0, v_a_4421_);
                        lean_ctor_set(v___x_4424_, 1, v___x_4423_);
                        lean_inc_ref(v___x_4424_);
                        v___x_4425_ = l_Lean_mkConst(v___x_4422_, v___x_4424_);
                        lean_inc_ref(v_op_4195_);
                        lean_inc_ref(v_binderType_4383_);
                        v___x_4426_ = l_Lean_mkAppB(v___x_4425_, v_binderType_4383_, v_op_4195_);
                        v___x_4427_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                            v___x_4426_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if lean_obj_tag(v___x_4427_) == 0 {
                            v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
                            v_isSharedCheck_4537_ = (!lean_is_exclusive(v___x_4427_)) as u8;
                            if v_isSharedCheck_4537_ == 0 {
                                v___x_4430_ = v___x_4427_;
                                v_isShared_4431_ = v_isSharedCheck_4537_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_4428_);
                                lean_dec(v___x_4427_);
                                v___x_4430_ = lean_box(0);
                                v_isShared_4431_ = v_isSharedCheck_4537_;
                                state = 23;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_4424_, 2);
                            lean_dec(v_a_4421_);
                            lean_dec(v_a_4415_);
                            lean_dec_ref(v_binderType_4383_);
                            lean_dec_ref(v_op_4195_);
                            v_a_4538_ = lean_ctor_get(v___x_4427_, 0);
                            v_isSharedCheck_4545_ = (!lean_is_exclusive(v___x_4427_)) as u8;
                            if v_isSharedCheck_4545_ == 0 {
                                v___x_4540_ = v___x_4427_;
                                v_isShared_4541_ = v_isSharedCheck_4545_;
                                state = 43;
                                continue;
                            } else {
                                lean_inc(v_a_4538_);
                                lean_dec(v___x_4427_);
                                v___x_4540_ = lean_box(0);
                                v_isShared_4541_ = v_isSharedCheck_4545_;
                                state = 43;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4415_);
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4546_ = lean_ctor_get(v___x_4420_, 0);
                        v_isSharedCheck_4553_ = (!lean_is_exclusive(v___x_4420_)) as u8;
                        if v_isSharedCheck_4553_ == 0 {
                            v___x_4548_ = v___x_4420_;
                            v_isShared_4549_ = v_isSharedCheck_4553_;
                            state = 45;
                            continue;
                        } else {
                            lean_inc(v_a_4546_);
                            lean_dec(v___x_4420_);
                            v___x_4548_ = lean_box(0);
                            v_isShared_4549_ = v_isSharedCheck_4553_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4415_);
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_op_4195_);
                    v___x_4554_ = lean_box(0);
                    if v_isShared_4418_ == 0 {
                        lean_ctor_set(v___x_4417_, 0, v___x_4554_);
                        v___x_4556_ = v___x_4417_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
                        v___x_4556_ = v_reuseFailAlloc_4557_;
                        state = 47;
                        continue;
                    }
                }
            }
            23 => {
                if lean_obj_tag(v_a_4428_) == 1 {
                    lean_del_object(v___x_4430_);
                    v_val_4432_ = lean_ctor_get(v_a_4428_, 0);
                    v_isSharedCheck_4532_ = (!lean_is_exclusive(v_a_4428_)) as u8;
                    if v_isSharedCheck_4532_ == 0 {
                        v___x_4434_ = v_a_4428_;
                        v_isShared_4435_ = v_isSharedCheck_4532_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_val_4432_);
                        lean_dec(v_a_4428_);
                        v___x_4434_ = lean_box(0);
                        v_isShared_4435_ = v_isSharedCheck_4532_;
                        state = 24;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4428_);
                    lean_dec_ref_known(v___x_4424_, 2);
                    lean_dec(v_a_4421_);
                    lean_dec(v_a_4415_);
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_op_4195_);
                    v___x_4533_ = lean_box(0);
                    if v_isShared_4431_ == 0 {
                        lean_ctor_set(v___x_4430_, 0, v___x_4533_);
                        v___x_4535_ = v___x_4430_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
                        v___x_4535_ = v_reuseFailAlloc_4536_;
                        state = 42;
                        continue;
                    }
                }
            }
            24 => {
                v___x_4436_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23;
                lean_inc_ref(v___x_4424_);
                v___x_4437_ = l_Lean_mkConst(v___x_4436_, v___x_4424_);
                lean_inc_ref(v_op_4195_);
                lean_inc_ref(v_binderType_4383_);
                v___x_4438_ = l_Lean_mkAppB(v___x_4437_, v_binderType_4383_, v_op_4195_);
                v___x_4439_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_4438_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if lean_obj_tag(v___x_4439_) == 0 {
                    v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
                    lean_inc(v_a_4440_);
                    lean_dec_ref_known(v___x_4439_, 1);
                    v___x_4441_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25;
                    lean_inc_ref(v___x_4424_);
                    v___x_4442_ = l_Lean_mkConst(v___x_4441_, v___x_4424_);
                    lean_inc_ref(v_op_4195_);
                    lean_inc_ref(v_binderType_4383_);
                    v___x_4443_ = l_Lean_mkAppB(v___x_4442_, v_binderType_4383_, v_op_4195_);
                    v___x_4444_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_4443_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if lean_obj_tag(v___x_4444_) == 0 {
                        v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
                        lean_inc(v_a_4445_);
                        lean_dec_ref_known(v___x_4444_, 1);
                        lean_inc_ref(v_binderType_4383_);
                        if v_isShared_4435_ == 0 {
                            lean_ctor_set(v___x_4434_, 0, v_binderType_4383_);
                            v___x_4447_ = v___x_4434_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_binderType_4383_);
                            v___x_4447_ = v_reuseFailAlloc_4515_;
                            state = 25;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4440_);
                        lean_del_object(v___x_4434_);
                        lean_dec(v_val_4432_);
                        lean_dec_ref_known(v___x_4424_, 2);
                        lean_dec(v_a_4421_);
                        lean_dec(v_a_4415_);
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4516_ = lean_ctor_get(v___x_4444_, 0);
                        v_isSharedCheck_4523_ = (!lean_is_exclusive(v___x_4444_)) as u8;
                        if v_isSharedCheck_4523_ == 0 {
                            v___x_4518_ = v___x_4444_;
                            v_isShared_4519_ = v_isSharedCheck_4523_;
                            state = 38;
                            continue;
                        } else {
                            lean_inc(v_a_4516_);
                            lean_dec(v___x_4444_);
                            v___x_4518_ = lean_box(0);
                            v_isShared_4519_ = v_isSharedCheck_4523_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4434_);
                    lean_dec(v_val_4432_);
                    lean_dec_ref_known(v___x_4424_, 2);
                    lean_dec(v_a_4421_);
                    lean_dec(v_a_4415_);
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_op_4195_);
                    v_a_4524_ = lean_ctor_get(v___x_4439_, 0);
                    v_isSharedCheck_4531_ = (!lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4531_ == 0 {
                        v___x_4526_ = v___x_4439_;
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_4524_);
                        lean_dec(v___x_4439_);
                        v___x_4526_ = lean_box(0);
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 40;
                        continue;
                    }
                }
            }
            25 => {
                v___x_4448_ = 0;
                v___x_4449_ = lean_box(0);
                v___x_4450_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_4447_,
                    v___x_4448_,
                    v___x_4449_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if lean_obj_tag(v___x_4450_) == 0 {
                    v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
                    lean_inc_n(v_a_4451_, 2);
                    lean_dec_ref_known(v___x_4450_, 1);
                    v___x_4452_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27;
                    v___x_4453_ = l_Lean_mkConst(v___x_4452_, v___x_4424_);
                    lean_inc_ref(v_op_4195_);
                    lean_inc_ref(v_binderType_4383_);
                    v___x_4454_ =
                        l_Lean_mkApp3(v___x_4453_, v_binderType_4383_, v_op_4195_, v_a_4451_);
                    v___x_4455_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_4454_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if lean_obj_tag(v___x_4455_) == 0 {
                        v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
                        lean_inc(v_a_4456_);
                        lean_dec_ref_known(v___x_4455_, 1);
                        if lean_obj_tag(v_a_4456_) == 1 {
                            v___x_4457_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_a_4451_, v___y_4373_);
                            v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
                            v_isSharedCheck_4496_ = (!lean_is_exclusive(v___x_4457_)) as u8;
                            if v_isSharedCheck_4496_ == 0 {
                                v___x_4460_ = v___x_4457_;
                                v_isShared_4461_ = v_isSharedCheck_4496_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_4458_);
                                lean_dec(v___x_4457_);
                                v___x_4460_ = lean_box(0);
                                v_isShared_4461_ = v_isSharedCheck_4496_;
                                state = 26;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4456_);
                            lean_dec(v_a_4451_);
                            v___x_4497_ = lean_box(0);
                            v___x_4498_ = (lean_unbox(v_a_4415_) as u8);
                            lean_dec(v_a_4415_);
                            lean_inc(v_a_4440_);
                            lean_inc(v_a_4445_);
                            v___y_4309_ = v_val_4432_;
                            v___y_4310_ = v___x_4498_;
                            v___y_4311_ = v_binderType_4383_;
                            v___y_4312_ = v_a_4445_;
                            v___y_4313_ = v_a_4440_;
                            v___y_4314_ = v_a_4421_;
                            v___y_4315_ = v_a_4445_;
                            v___y_4316_ = v_a_4440_;
                            v_fst_4317_ = v___x_4497_;
                            v_snd_4318_ = v___x_4497_;
                            v___y_4319_ = v___y_4366_;
                            v___y_4320_ = v___y_4367_;
                            v___y_4321_ = v___y_4368_;
                            v___y_4322_ = v___y_4369_;
                            v___y_4323_ = v___y_4370_;
                            v___y_4324_ = v___y_4371_;
                            v___y_4325_ = v___y_4372_;
                            v___y_4326_ = v___y_4373_;
                            v___y_4327_ = v___y_4374_;
                            v___y_4328_ = v___y_4375_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4451_);
                        lean_dec(v_a_4445_);
                        lean_dec(v_a_4440_);
                        lean_dec(v_val_4432_);
                        lean_dec(v_a_4421_);
                        lean_dec(v_a_4415_);
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4499_ = lean_ctor_get(v___x_4455_, 0);
                        v_isSharedCheck_4506_ = (!lean_is_exclusive(v___x_4455_)) as u8;
                        if v_isSharedCheck_4506_ == 0 {
                            v___x_4501_ = v___x_4455_;
                            v_isShared_4502_ = v_isSharedCheck_4506_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_4499_);
                            lean_dec(v___x_4455_);
                            v___x_4501_ = lean_box(0);
                            v_isShared_4502_ = v_isSharedCheck_4506_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4445_);
                    lean_dec(v_a_4440_);
                    lean_dec(v_val_4432_);
                    lean_dec_ref_known(v___x_4424_, 2);
                    lean_dec(v_a_4421_);
                    lean_dec(v_a_4415_);
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_op_4195_);
                    v_a_4507_ = lean_ctor_get(v___x_4450_, 0);
                    v_isSharedCheck_4514_ = (!lean_is_exclusive(v___x_4450_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4509_ = v___x_4450_;
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_4507_);
                        lean_dec(v___x_4450_);
                        v___x_4509_ = lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 36;
                        continue;
                    }
                }
            }
            26 => {
                v___x_4462_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                    v_a_4458_,
                    v___y_4367_,
                    v___y_4368_,
                    v___y_4369_,
                    v___y_4370_,
                    v___y_4371_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if lean_obj_tag(v___x_4462_) == 0 {
                    v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
                    lean_inc(v_a_4463_);
                    lean_dec_ref_known(v___x_4462_, 1);
                    v___x_4464_ = l_Lean_Meta_Grind_getGeneration___redArg(v_op_4195_, v___y_4366_);
                    if lean_obj_tag(v___x_4464_) == 0 {
                        v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
                        lean_inc(v_a_4465_);
                        lean_dec_ref_known(v___x_4464_, 1);
                        v___x_4466_ = lean_box(0);
                        lean_inc(v___y_4375_);
                        lean_inc_ref(v___y_4374_);
                        lean_inc(v___y_4373_);
                        lean_inc_ref(v___y_4372_);
                        lean_inc(v___y_4371_);
                        lean_inc_ref(v___y_4370_);
                        lean_inc(v___y_4369_);
                        lean_inc_ref(v___y_4368_);
                        lean_inc(v___y_4367_);
                        lean_inc(v___y_4366_);
                        lean_inc(v_a_4463_);
                        v___x_4467_ = lean_grind_internalize(
                            v_a_4463_,
                            v_a_4465_,
                            v___x_4466_,
                            v___y_4366_,
                            v___y_4367_,
                            v___y_4368_,
                            v___y_4369_,
                            v___y_4370_,
                            v___y_4371_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if lean_obj_tag(v___x_4467_) == 0 {
                            lean_dec_ref_known(v___x_4467_, 1);
                            if v_isShared_4461_ == 0 {
                                lean_ctor_set_tag(v___x_4460_, 1);
                                lean_ctor_set(v___x_4460_, 0, v_a_4463_);
                                v___x_4469_ = v___x_4460_;
                                state = 27;
                                continue;
                            } else {
                                v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4463_);
                                v___x_4469_ = v_reuseFailAlloc_4471_;
                                state = 27;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4463_);
                            lean_del_object(v___x_4460_);
                            lean_dec_ref_known(v_a_4456_, 1);
                            lean_dec(v_a_4445_);
                            lean_dec(v_a_4440_);
                            lean_dec(v_val_4432_);
                            lean_dec(v_a_4421_);
                            lean_dec(v_a_4415_);
                            lean_dec_ref(v_binderType_4383_);
                            lean_dec_ref(v_op_4195_);
                            v_a_4472_ = lean_ctor_get(v___x_4467_, 0);
                            v_isSharedCheck_4479_ = (!lean_is_exclusive(v___x_4467_)) as u8;
                            if v_isSharedCheck_4479_ == 0 {
                                v___x_4474_ = v___x_4467_;
                                v_isShared_4475_ = v_isSharedCheck_4479_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_4472_);
                                lean_dec(v___x_4467_);
                                v___x_4474_ = lean_box(0);
                                v_isShared_4475_ = v_isSharedCheck_4479_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4463_);
                        lean_del_object(v___x_4460_);
                        lean_dec_ref_known(v_a_4456_, 1);
                        lean_dec(v_a_4445_);
                        lean_dec(v_a_4440_);
                        lean_dec(v_val_4432_);
                        lean_dec(v_a_4421_);
                        lean_dec(v_a_4415_);
                        lean_dec_ref(v_binderType_4383_);
                        lean_dec_ref(v_op_4195_);
                        v_a_4480_ = lean_ctor_get(v___x_4464_, 0);
                        v_isSharedCheck_4487_ = (!lean_is_exclusive(v___x_4464_)) as u8;
                        if v_isSharedCheck_4487_ == 0 {
                            v___x_4482_ = v___x_4464_;
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_4480_);
                            lean_dec(v___x_4464_);
                            v___x_4482_ = lean_box(0);
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4460_);
                    lean_dec_ref_known(v_a_4456_, 1);
                    lean_dec(v_a_4445_);
                    lean_dec(v_a_4440_);
                    lean_dec(v_val_4432_);
                    lean_dec(v_a_4421_);
                    lean_dec(v_a_4415_);
                    lean_dec_ref(v_binderType_4383_);
                    lean_dec_ref(v_op_4195_);
                    v_a_4488_ = lean_ctor_get(v___x_4462_, 0);
                    v_isSharedCheck_4495_ = (!lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4495_ == 0 {
                        v___x_4490_ = v___x_4462_;
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_a_4488_);
                        lean_dec(v___x_4462_);
                        v___x_4490_ = lean_box(0);
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 32;
                        continue;
                    }
                }
            }
            27 => {
                v___x_4470_ = (lean_unbox(v_a_4415_) as u8);
                lean_dec(v_a_4415_);
                lean_inc(v_a_4440_);
                lean_inc(v_a_4445_);
                v___y_4309_ = v_val_4432_;
                v___y_4310_ = v___x_4470_;
                v___y_4311_ = v_binderType_4383_;
                v___y_4312_ = v_a_4445_;
                v___y_4313_ = v_a_4440_;
                v___y_4314_ = v_a_4421_;
                v___y_4315_ = v_a_4445_;
                v___y_4316_ = v_a_4440_;
                v_fst_4317_ = v_a_4456_;
                v_snd_4318_ = v___x_4469_;
                v___y_4319_ = v___y_4366_;
                v___y_4320_ = v___y_4367_;
                v___y_4321_ = v___y_4368_;
                v___y_4322_ = v___y_4369_;
                v___y_4323_ = v___y_4370_;
                v___y_4324_ = v___y_4371_;
                v___y_4325_ = v___y_4372_;
                v___y_4326_ = v___y_4373_;
                v___y_4327_ = v___y_4374_;
                v___y_4328_ = v___y_4375_;
                state = 10;
                continue;
            }
            28 => {
                if v_isShared_4475_ == 0 {
                    v___x_4477_ = v___x_4474_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
                    v___x_4477_ = v_reuseFailAlloc_4478_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4477_;
            }
            30 => {
                if v_isShared_4483_ == 0 {
                    v___x_4485_ = v___x_4482_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
                    v___x_4485_ = v_reuseFailAlloc_4486_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4485_;
            }
            32 => {
                if v_isShared_4491_ == 0 {
                    v___x_4493_ = v___x_4490_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
                    v___x_4493_ = v_reuseFailAlloc_4494_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4493_;
            }
            34 => {
                if v_isShared_4502_ == 0 {
                    v___x_4504_ = v___x_4501_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
                    v___x_4504_ = v_reuseFailAlloc_4505_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4504_;
            }
            36 => {
                if v_isShared_4510_ == 0 {
                    v___x_4512_ = v___x_4509_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4512_;
            }
            38 => {
                if v_isShared_4519_ == 0 {
                    v___x_4521_ = v___x_4518_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
                    v___x_4521_ = v_reuseFailAlloc_4522_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4521_;
            }
            40 => {
                if v_isShared_4527_ == 0 {
                    v___x_4529_ = v___x_4526_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
                    v___x_4529_ = v_reuseFailAlloc_4530_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4529_;
            }
            42 => {
                return v___x_4535_;
            }
            43 => {
                if v_isShared_4541_ == 0 {
                    v___x_4543_ = v___x_4540_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4543_;
            }
            45 => {
                if v_isShared_4549_ == 0 {
                    v___x_4551_ = v___x_4548_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
                    v___x_4551_ = v_reuseFailAlloc_4552_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4551_;
            }
            47 => {
                return v___x_4556_;
            }
            48 => {
                if v_isShared_4562_ == 0 {
                    v___x_4564_ = v___x_4561_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
                    v___x_4564_ = v_reuseFailAlloc_4565_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4564_;
            }
            50 => {
                if v_isShared_4571_ == 0 {
                    v___x_4573_ = v___x_4570_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
                    v___x_4573_ = v_reuseFailAlloc_4574_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_4573_;
            }
            52 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4582_;
            }
            54 => {
                return v___x_4587_;
            }
            55 => {
                return v___x_4591_;
            }
            56 => {
                if v_isShared_4597_ == 0 {
                    v___x_4599_ = v___x_4596_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
                    v___x_4599_ = v_reuseFailAlloc_4600_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_4599_;
            }
            58 => {
                return v___x_4604_;
            }
            59 => {
                return v___x_4608_;
            }
            60 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_4616_;
            }
            62 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(
    mut v_op_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
    mut v_a_4635_: *mut LeanObject,
    mut v_a_4636_: *mut LeanObject,
    mut v_a_4637_: *mut LeanObject,
    mut v_a_4638_: *mut LeanObject,
    mut v_a_4639_: *mut LeanObject,
    mut v_a_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
    mut v_a_4642_: *mut LeanObject,
    mut v_a_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4644_: *mut LeanObject = core::ptr::null_mut();
    v_res_4644_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(
        v_op_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_,
        v_a_4640_, v_a_4641_, v_a_4642_,
    );
    lean_dec(v_a_4642_);
    lean_dec_ref(v_a_4641_);
    lean_dec(v_a_4640_);
    lean_dec_ref(v_a_4639_);
    lean_dec(v_a_4638_);
    lean_dec_ref(v_a_4637_);
    lean_dec(v_a_4636_);
    lean_dec_ref(v_a_4635_);
    lean_dec(v_a_4634_);
    lean_dec(v_a_4633_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(
    mut v_cls_4645_: *mut LeanObject,
    mut v_msg_4646_: *mut LeanObject,
    mut v___y_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    v___x_4658_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_4645_, v_msg_4646_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
    return v___x_4658_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(
    mut v_cls_4659_: *mut LeanObject,
    mut v_msg_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
    mut v___y_4668_: *mut LeanObject,
    mut v___y_4669_: *mut LeanObject,
    mut v___y_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4672_: *mut LeanObject = core::ptr::null_mut();
    v_res_4672_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_4659_, v_msg_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
    lean_dec(v___y_4670_);
    lean_dec_ref(v___y_4669_);
    lean_dec(v___y_4668_);
    lean_dec_ref(v___y_4667_);
    lean_dec(v___y_4666_);
    lean_dec_ref(v___y_4665_);
    lean_dec(v___y_4664_);
    lean_dec_ref(v___y_4663_);
    lean_dec(v___y_4662_);
    lean_dec(v___y_4661_);
    return v_res_4672_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(
    mut v_00_u03b2_4673_: *mut LeanObject,
    mut v_m_4674_: *mut LeanObject,
    mut v_a_4675_: *mut LeanObject,
) -> u8 {
    let mut v___x_4676_: u8 = 0;
    v___x_4676_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_4674_, v_a_4675_);
    return v___x_4676_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(
    mut v_00_u03b2_4677_: *mut LeanObject,
    mut v_m_4678_: *mut LeanObject,
    mut v_a_4679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4680_: u8 = 0;
    let mut v_r_4681_: *mut LeanObject = core::ptr::null_mut();
    v_res_4680_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(v_00_u03b2_4677_, v_m_4678_, v_a_4679_);
    lean_dec(v_a_4679_);
    lean_dec_ref(v_m_4678_);
    v_r_4681_ = lean_box((v_res_4680_) as usize);
    return v_r_4681_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(
    mut v_op_4682_: *mut LeanObject,
    mut v_a_4683_: *mut LeanObject,
    mut v_s_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_4685_ = lean_ctor_get(v_s_4684_, 0);
                v_opIdOf_4686_ = lean_ctor_get(v_s_4684_, 1);
                v_exprToOpIds_4687_ = lean_ctor_get(v_s_4684_, 2);
                v_steps_4688_ = lean_ctor_get(v_s_4684_, 3);
                v_isSharedCheck_4696_ = (!lean_is_exclusive(v_s_4684_)) as u8;
                if v_isSharedCheck_4696_ == 0 {
                    v___x_4690_ = v_s_4684_;
                    v_isShared_4691_ = v_isSharedCheck_4696_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_4688_);
                    lean_inc(v_exprToOpIds_4687_);
                    lean_inc(v_opIdOf_4686_);
                    lean_inc(v_structs_4685_);
                    lean_dec(v_s_4684_);
                    v___x_4690_ = lean_box(0);
                    v_isShared_4691_ = v_isSharedCheck_4696_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4692_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_opIdOf_4686_, v_op_4682_, v_a_4683_);
                if v_isShared_4691_ == 0 {
                    lean_ctor_set(v___x_4690_, 1, v___x_4692_);
                    v___x_4694_ = v___x_4690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_structs_4685_);
                    lean_ctor_set(v_reuseFailAlloc_4695_, 1, v___x_4692_);
                    lean_ctor_set(v_reuseFailAlloc_4695_, 2, v_exprToOpIds_4687_);
                    lean_ctor_set(v_reuseFailAlloc_4695_, 3, v_steps_4688_);
                    v___x_4694_ = v_reuseFailAlloc_4695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId_x3f(
    mut v_op_4697_: *mut LeanObject,
    mut v_a_4698_: *mut LeanObject,
    mut v_a_4699_: *mut LeanObject,
    mut v_a_4700_: *mut LeanObject,
    mut v_a_4701_: *mut LeanObject,
    mut v_a_4702_: *mut LeanObject,
    mut v_a_4703_: *mut LeanObject,
    mut v_a_4704_: *mut LeanObject,
    mut v_a_4705_: *mut LeanObject,
    mut v_a_4706_: *mut LeanObject,
    mut v_a_4707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4713_: u8 = 0;
    let mut v_opIdOf_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut v_unused_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_a_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4745_: u8 = 0;
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4709_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_4698_, v_a_4706_);
                if lean_obj_tag(v___x_4709_) == 0 {
                    v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
                    v_isSharedCheck_4741_ = (!lean_is_exclusive(v___x_4709_)) as u8;
                    if v_isSharedCheck_4741_ == 0 {
                        v___x_4712_ = v___x_4709_;
                        v_isShared_4713_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4710_);
                        lean_dec(v___x_4709_);
                        v___x_4712_ = lean_box(0);
                        v_isShared_4713_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_op_4697_);
                    v_a_4742_ = lean_ctor_get(v___x_4709_, 0);
                    v_isSharedCheck_4749_ = (!lean_is_exclusive(v___x_4709_)) as u8;
                    if v_isSharedCheck_4749_ == 0 {
                        v___x_4744_ = v___x_4709_;
                        v_isShared_4745_ = v_isSharedCheck_4749_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4742_);
                        lean_dec(v___x_4709_);
                        v___x_4744_ = lean_box(0);
                        v_isShared_4745_ = v_isSharedCheck_4749_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_opIdOf_4714_ = lean_ctor_get(v_a_4710_, 1);
                lean_inc_ref(v_opIdOf_4714_);
                lean_dec(v_a_4710_);
                v___x_4715_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_opIdOf_4714_, v_op_4697_);
                lean_dec_ref(v_opIdOf_4714_);
                if lean_obj_tag(v___x_4715_) == 1 {
                    lean_dec_ref(v_op_4697_);
                    v_val_4716_ = lean_ctor_get(v___x_4715_, 0);
                    lean_inc(v_val_4716_);
                    lean_dec_ref_known(v___x_4715_, 1);
                    if v_isShared_4713_ == 0 {
                        lean_ctor_set(v___x_4712_, 0, v_val_4716_);
                        v___x_4718_ = v___x_4712_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_val_4716_);
                        v___x_4718_ = v_reuseFailAlloc_4719_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4715_);
                    lean_del_object(v___x_4712_);
                    lean_inc_ref(v_op_4697_);
                    v___x_4720_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
                    if lean_obj_tag(v___x_4720_) == 0 {
                        v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
                        lean_inc_n(v_a_4721_, 2);
                        lean_dec_ref_known(v___x_4720_, 1);
                        v___f_4722_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0 as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_4722_, 0, v_op_4697_);
                        lean_closure_set(v___f_4722_, 1, v_a_4721_);
                        v___x_4723_ = l_Lean_Meta_Grind_AC_acExt;
                        v___x_4724_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4723_, v___f_4722_, v_a_4698_);
                        if lean_obj_tag(v___x_4724_) == 0 {
                            v_isSharedCheck_4731_ = (!lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4731_ == 0 {
                                v_unused_4732_ = lean_ctor_get(v___x_4724_, 0);
                                lean_dec(v_unused_4732_);
                                v___x_4726_ = v___x_4724_;
                                v_isShared_4727_ = v_isSharedCheck_4731_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_4724_);
                                v___x_4726_ = lean_box(0);
                                v_isShared_4727_ = v_isSharedCheck_4731_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4721_);
                            v_a_4733_ = lean_ctor_get(v___x_4724_, 0);
                            v_isSharedCheck_4740_ = (!lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4740_ == 0 {
                                v___x_4735_ = v___x_4724_;
                                v_isShared_4736_ = v_isSharedCheck_4740_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4733_);
                                lean_dec(v___x_4724_);
                                v___x_4735_ = lean_box(0);
                                v_isShared_4736_ = v_isSharedCheck_4740_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_op_4697_);
                        return v___x_4720_;
                    }
                }
            }
            2 => {
                return v___x_4718_;
            }
            3 => {
                if v_isShared_4727_ == 0 {
                    lean_ctor_set(v___x_4726_, 0, v_a_4721_);
                    v___x_4729_ = v___x_4726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4721_);
                    v___x_4729_ = v_reuseFailAlloc_4730_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4729_;
            }
            5 => {
                if v_isShared_4736_ == 0 {
                    v___x_4738_ = v___x_4735_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
                    v___x_4738_ = v_reuseFailAlloc_4739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4738_;
            }
            7 => {
                if v_isShared_4745_ == 0 {
                    v___x_4747_ = v___x_4744_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
                    v___x_4747_ = v_reuseFailAlloc_4748_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(
    mut v_op_4750_: *mut LeanObject,
    mut v_a_4751_: *mut LeanObject,
    mut v_a_4752_: *mut LeanObject,
    mut v_a_4753_: *mut LeanObject,
    mut v_a_4754_: *mut LeanObject,
    mut v_a_4755_: *mut LeanObject,
    mut v_a_4756_: *mut LeanObject,
    mut v_a_4757_: *mut LeanObject,
    mut v_a_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
    mut v_a_4761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4762_: *mut LeanObject = core::ptr::null_mut();
    v_res_4762_ = l_Lean_Meta_Grind_AC_getOpId_x3f(
        v_op_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_,
        v_a_4758_, v_a_4759_, v_a_4760_,
    );
    lean_dec(v_a_4760_);
    lean_dec_ref(v_a_4759_);
    lean_dec(v_a_4758_);
    lean_dec_ref(v_a_4757_);
    lean_dec(v_a_4756_);
    lean_dec_ref(v_a_4755_);
    lean_dec(v_a_4754_);
    lean_dec_ref(v_a_4753_);
    lean_dec(v_a_4752_);
    lean_dec(v_a_4751_);
    return v_res_4762_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_isOp_x3f(
    mut v_e_4763_: *mut LeanObject,
    mut v_a_4764_: *mut LeanObject,
    mut v_a_4765_: *mut LeanObject,
    mut v_a_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
    mut v_a_4771_: *mut LeanObject,
    mut v_a_4772_: *mut LeanObject,
    mut v_a_4773_: *mut LeanObject,
    mut v_a_4774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4777_: u8 = 0;
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: u8 = 0;
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut v_a_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4808_ = l_Lean_Expr_isApp(v_e_4763_);
                if v___x_4808_ == 0 {
                    v___y_4777_ = v___x_4808_;
                    state = 1;
                    continue;
                } else {
                    v___x_4809_ = l_Lean_Expr_appFn_x21(v_e_4763_);
                    v___x_4810_ = l_Lean_Expr_isApp(v___x_4809_);
                    lean_dec_ref(v___x_4809_);
                    v___y_4777_ = v___x_4810_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4777_ == 0 {
                    v___x_4778_ = lean_box(0);
                    v___x_4779_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4779_, 0, v___x_4778_);
                    return v___x_4779_;
                } else {
                    v___x_4780_ = l_Lean_Meta_Grind_AC_getOp(
                        v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_,
                        v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_,
                    );
                    if lean_obj_tag(v___x_4780_) == 0 {
                        v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
                        v_isSharedCheck_4799_ = (!lean_is_exclusive(v___x_4780_)) as u8;
                        if v_isSharedCheck_4799_ == 0 {
                            v___x_4783_ = v___x_4780_;
                            v_isShared_4784_ = v_isSharedCheck_4799_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4781_);
                            lean_dec(v___x_4780_);
                            v___x_4783_ = lean_box(0);
                            v_isShared_4784_ = v_isSharedCheck_4799_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_4800_ = lean_ctor_get(v___x_4780_, 0);
                        v_isSharedCheck_4807_ = (!lean_is_exclusive(v___x_4780_)) as u8;
                        if v_isSharedCheck_4807_ == 0 {
                            v___x_4802_ = v___x_4780_;
                            v_isShared_4803_ = v_isSharedCheck_4807_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4800_);
                            lean_dec(v___x_4780_);
                            v___x_4802_ = lean_box(0);
                            v_isShared_4803_ = v_isSharedCheck_4807_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4785_ = l_Lean_Expr_appFn_x21(v_e_4763_);
                v___x_4786_ = l_Lean_Expr_appFn_x21(v___x_4785_);
                v___x_4787_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_4786_,
                        v_a_4781_,
                    );
                lean_dec(v_a_4781_);
                lean_dec_ref(v___x_4786_);
                if v___x_4787_ == 0 {
                    lean_dec_ref(v___x_4785_);
                    v___x_4788_ = lean_box(0);
                    if v_isShared_4784_ == 0 {
                        lean_ctor_set(v___x_4783_, 0, v___x_4788_);
                        v___x_4790_ = v___x_4783_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4788_);
                        v___x_4790_ = v_reuseFailAlloc_4791_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4792_ = l_Lean_Expr_appArg_x21(v___x_4785_);
                    lean_dec_ref(v___x_4785_);
                    v___x_4793_ = l_Lean_Expr_appArg_x21(v_e_4763_);
                    v___x_4794_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4794_, 0, v___x_4792_);
                    lean_ctor_set(v___x_4794_, 1, v___x_4793_);
                    v___x_4795_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4795_, 0, v___x_4794_);
                    if v_isShared_4784_ == 0 {
                        lean_ctor_set(v___x_4783_, 0, v___x_4795_);
                        v___x_4797_ = v___x_4783_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
                        v___x_4797_ = v_reuseFailAlloc_4798_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4790_;
            }
            4 => {
                return v___x_4797_;
            }
            5 => {
                if v_isShared_4803_ == 0 {
                    v___x_4805_ = v___x_4802_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
                    v___x_4805_ = v_reuseFailAlloc_4806_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_isOp_x3f___boxed(
    mut v_e_4811_: *mut LeanObject,
    mut v_a_4812_: *mut LeanObject,
    mut v_a_4813_: *mut LeanObject,
    mut v_a_4814_: *mut LeanObject,
    mut v_a_4815_: *mut LeanObject,
    mut v_a_4816_: *mut LeanObject,
    mut v_a_4817_: *mut LeanObject,
    mut v_a_4818_: *mut LeanObject,
    mut v_a_4819_: *mut LeanObject,
    mut v_a_4820_: *mut LeanObject,
    mut v_a_4821_: *mut LeanObject,
    mut v_a_4822_: *mut LeanObject,
    mut v_a_4823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4824_: *mut LeanObject = core::ptr::null_mut();
    v_res_4824_ = l_Lean_Meta_Grind_AC_isOp_x3f(
        v_e_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_,
        v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_,
    );
    lean_dec(v_a_4822_);
    lean_dec_ref(v_a_4821_);
    lean_dec(v_a_4820_);
    lean_dec_ref(v_a_4819_);
    lean_dec(v_a_4818_);
    lean_dec_ref(v_a_4817_);
    lean_dec(v_a_4816_);
    lean_dec_ref(v_a_4815_);
    lean_dec(v_a_4814_);
    lean_dec(v_a_4813_);
    lean_dec(v_a_4812_);
    lean_dec_ref(v_e_4811_);
    return v_res_4824_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_isCommutative(
    mut v_a_4825_: *mut LeanObject,
    mut v_a_4826_: *mut LeanObject,
    mut v_a_4827_: *mut LeanObject,
    mut v_a_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
    mut v_a_4830_: *mut LeanObject,
    mut v_a_4831_: *mut LeanObject,
    mut v_a_4832_: *mut LeanObject,
    mut v_a_4833_: *mut LeanObject,
    mut v_a_4834_: *mut LeanObject,
    mut v_a_4835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4841_: u8 = 0;
    let mut v_commInst_x3f_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: u8 = 0;
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: u8 = 0;
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4853_: u8 = 0;
    let mut v_a_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4857_: u8 = 0;
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4837_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_,
                    v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_,
                );
                if lean_obj_tag(v___x_4837_) == 0 {
                    v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
                    v_isSharedCheck_4853_ = (!lean_is_exclusive(v___x_4837_)) as u8;
                    if v_isSharedCheck_4853_ == 0 {
                        v___x_4840_ = v___x_4837_;
                        v_isShared_4841_ = v_isSharedCheck_4853_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4838_);
                        lean_dec(v___x_4837_);
                        v___x_4840_ = lean_box(0);
                        v_isShared_4841_ = v_isSharedCheck_4853_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4854_ = lean_ctor_get(v___x_4837_, 0);
                    v_isSharedCheck_4861_ = (!lean_is_exclusive(v___x_4837_)) as u8;
                    if v_isSharedCheck_4861_ == 0 {
                        v___x_4856_ = v___x_4837_;
                        v_isShared_4857_ = v_isSharedCheck_4861_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4854_);
                        lean_dec(v___x_4837_);
                        v___x_4856_ = lean_box(0);
                        v_isShared_4857_ = v_isSharedCheck_4861_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_commInst_x3f_4842_ = lean_ctor_get(v_a_4838_, 7);
                lean_inc(v_commInst_x3f_4842_);
                lean_dec(v_a_4838_);
                if lean_obj_tag(v_commInst_x3f_4842_) == 0 {
                    v___x_4843_ = 0;
                    v___x_4844_ = lean_box((v___x_4843_) as usize);
                    if v_isShared_4841_ == 0 {
                        lean_ctor_set(v___x_4840_, 0, v___x_4844_);
                        v___x_4846_ = v___x_4840_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
                        v___x_4846_ = v_reuseFailAlloc_4847_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_commInst_x3f_4842_, 1);
                    v___x_4848_ = 1;
                    v___x_4849_ = lean_box((v___x_4848_) as usize);
                    if v_isShared_4841_ == 0 {
                        lean_ctor_set(v___x_4840_, 0, v___x_4849_);
                        v___x_4851_ = v___x_4840_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
                        v___x_4851_ = v_reuseFailAlloc_4852_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4846_;
            }
            3 => {
                return v___x_4851_;
            }
            4 => {
                if v_isShared_4857_ == 0 {
                    v___x_4859_ = v___x_4856_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
                    v___x_4859_ = v_reuseFailAlloc_4860_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_isCommutative___boxed(
    mut v_a_4862_: *mut LeanObject,
    mut v_a_4863_: *mut LeanObject,
    mut v_a_4864_: *mut LeanObject,
    mut v_a_4865_: *mut LeanObject,
    mut v_a_4866_: *mut LeanObject,
    mut v_a_4867_: *mut LeanObject,
    mut v_a_4868_: *mut LeanObject,
    mut v_a_4869_: *mut LeanObject,
    mut v_a_4870_: *mut LeanObject,
    mut v_a_4871_: *mut LeanObject,
    mut v_a_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4874_: *mut LeanObject = core::ptr::null_mut();
    v_res_4874_ = l_Lean_Meta_Grind_AC_isCommutative(
        v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_,
        v_a_4870_, v_a_4871_, v_a_4872_,
    );
    lean_dec(v_a_4872_);
    lean_dec_ref(v_a_4871_);
    lean_dec(v_a_4870_);
    lean_dec_ref(v_a_4869_);
    lean_dec(v_a_4868_);
    lean_dec_ref(v_a_4867_);
    lean_dec(v_a_4866_);
    lean_dec_ref(v_a_4865_);
    lean_dec(v_a_4864_);
    lean_dec(v_a_4863_);
    lean_dec(v_a_4862_);
    return v_res_4874_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_hasNeutral(
    mut v_a_4875_: *mut LeanObject,
    mut v_a_4876_: *mut LeanObject,
    mut v_a_4877_: *mut LeanObject,
    mut v_a_4878_: *mut LeanObject,
    mut v_a_4879_: *mut LeanObject,
    mut v_a_4880_: *mut LeanObject,
    mut v_a_4881_: *mut LeanObject,
    mut v_a_4882_: *mut LeanObject,
    mut v_a_4883_: *mut LeanObject,
    mut v_a_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4891_: u8 = 0;
    let mut v_neutralInst_x3f_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: u8 = 0;
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: u8 = 0;
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4903_: u8 = 0;
    let mut v_a_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4907_: u8 = 0;
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4887_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_,
                    v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_,
                );
                if lean_obj_tag(v___x_4887_) == 0 {
                    v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
                    v_isSharedCheck_4903_ = (!lean_is_exclusive(v___x_4887_)) as u8;
                    if v_isSharedCheck_4903_ == 0 {
                        v___x_4890_ = v___x_4887_;
                        v_isShared_4891_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4888_);
                        lean_dec(v___x_4887_);
                        v___x_4890_ = lean_box(0);
                        v_isShared_4891_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4904_ = lean_ctor_get(v___x_4887_, 0);
                    v_isSharedCheck_4911_ = (!lean_is_exclusive(v___x_4887_)) as u8;
                    if v_isSharedCheck_4911_ == 0 {
                        v___x_4906_ = v___x_4887_;
                        v_isShared_4907_ = v_isSharedCheck_4911_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4904_);
                        lean_dec(v___x_4887_);
                        v___x_4906_ = lean_box(0);
                        v_isShared_4907_ = v_isSharedCheck_4911_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_neutralInst_x3f_4892_ = lean_ctor_get(v_a_4888_, 8);
                lean_inc(v_neutralInst_x3f_4892_);
                lean_dec(v_a_4888_);
                if lean_obj_tag(v_neutralInst_x3f_4892_) == 0 {
                    v___x_4893_ = 0;
                    v___x_4894_ = lean_box((v___x_4893_) as usize);
                    if v_isShared_4891_ == 0 {
                        lean_ctor_set(v___x_4890_, 0, v___x_4894_);
                        v___x_4896_ = v___x_4890_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4894_);
                        v___x_4896_ = v_reuseFailAlloc_4897_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_neutralInst_x3f_4892_, 1);
                    v___x_4898_ = 1;
                    v___x_4899_ = lean_box((v___x_4898_) as usize);
                    if v_isShared_4891_ == 0 {
                        lean_ctor_set(v___x_4890_, 0, v___x_4899_);
                        v___x_4901_ = v___x_4890_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
                        v___x_4901_ = v_reuseFailAlloc_4902_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4896_;
            }
            3 => {
                return v___x_4901_;
            }
            4 => {
                if v_isShared_4907_ == 0 {
                    v___x_4909_ = v___x_4906_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4904_);
                    v___x_4909_ = v_reuseFailAlloc_4910_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_hasNeutral___boxed(
    mut v_a_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
    mut v_a_4917_: *mut LeanObject,
    mut v_a_4918_: *mut LeanObject,
    mut v_a_4919_: *mut LeanObject,
    mut v_a_4920_: *mut LeanObject,
    mut v_a_4921_: *mut LeanObject,
    mut v_a_4922_: *mut LeanObject,
    mut v_a_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4924_: *mut LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_Meta_Grind_AC_hasNeutral(
        v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_,
        v_a_4920_, v_a_4921_, v_a_4922_,
    );
    lean_dec(v_a_4922_);
    lean_dec_ref(v_a_4921_);
    lean_dec(v_a_4920_);
    lean_dec_ref(v_a_4919_);
    lean_dec(v_a_4918_);
    lean_dec_ref(v_a_4917_);
    lean_dec(v_a_4916_);
    lean_dec_ref(v_a_4915_);
    lean_dec(v_a_4914_);
    lean_dec(v_a_4913_);
    lean_dec(v_a_4912_);
    return v_res_4924_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_isIdempotent(
    mut v_a_4925_: *mut LeanObject,
    mut v_a_4926_: *mut LeanObject,
    mut v_a_4927_: *mut LeanObject,
    mut v_a_4928_: *mut LeanObject,
    mut v_a_4929_: *mut LeanObject,
    mut v_a_4930_: *mut LeanObject,
    mut v_a_4931_: *mut LeanObject,
    mut v_a_4932_: *mut LeanObject,
    mut v_a_4933_: *mut LeanObject,
    mut v_a_4934_: *mut LeanObject,
    mut v_a_4935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v_idempotentInst_x3f_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v_a_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4937_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_,
                    v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_,
                );
                if lean_obj_tag(v___x_4937_) == 0 {
                    v_a_4938_ = lean_ctor_get(v___x_4937_, 0);
                    v_isSharedCheck_4953_ = (!lean_is_exclusive(v___x_4937_)) as u8;
                    if v_isSharedCheck_4953_ == 0 {
                        v___x_4940_ = v___x_4937_;
                        v_isShared_4941_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4938_);
                        lean_dec(v___x_4937_);
                        v___x_4940_ = lean_box(0);
                        v_isShared_4941_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4954_ = lean_ctor_get(v___x_4937_, 0);
                    v_isSharedCheck_4961_ = (!lean_is_exclusive(v___x_4937_)) as u8;
                    if v_isSharedCheck_4961_ == 0 {
                        v___x_4956_ = v___x_4937_;
                        v_isShared_4957_ = v_isSharedCheck_4961_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4954_);
                        lean_dec(v___x_4937_);
                        v___x_4956_ = lean_box(0);
                        v_isShared_4957_ = v_isSharedCheck_4961_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_idempotentInst_x3f_4942_ = lean_ctor_get(v_a_4938_, 6);
                lean_inc(v_idempotentInst_x3f_4942_);
                lean_dec(v_a_4938_);
                if lean_obj_tag(v_idempotentInst_x3f_4942_) == 0 {
                    v___x_4943_ = 0;
                    v___x_4944_ = lean_box((v___x_4943_) as usize);
                    if v_isShared_4941_ == 0 {
                        lean_ctor_set(v___x_4940_, 0, v___x_4944_);
                        v___x_4946_ = v___x_4940_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
                        v___x_4946_ = v_reuseFailAlloc_4947_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_idempotentInst_x3f_4942_, 1);
                    v___x_4948_ = 1;
                    v___x_4949_ = lean_box((v___x_4948_) as usize);
                    if v_isShared_4941_ == 0 {
                        lean_ctor_set(v___x_4940_, 0, v___x_4949_);
                        v___x_4951_ = v___x_4940_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4949_);
                        v___x_4951_ = v_reuseFailAlloc_4952_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4946_;
            }
            3 => {
                return v___x_4951_;
            }
            4 => {
                if v_isShared_4957_ == 0 {
                    v___x_4959_ = v___x_4956_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
                    v___x_4959_ = v_reuseFailAlloc_4960_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_isIdempotent___boxed(
    mut v_a_4962_: *mut LeanObject,
    mut v_a_4963_: *mut LeanObject,
    mut v_a_4964_: *mut LeanObject,
    mut v_a_4965_: *mut LeanObject,
    mut v_a_4966_: *mut LeanObject,
    mut v_a_4967_: *mut LeanObject,
    mut v_a_4968_: *mut LeanObject,
    mut v_a_4969_: *mut LeanObject,
    mut v_a_4970_: *mut LeanObject,
    mut v_a_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
    mut v_a_4973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4974_: *mut LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Lean_Meta_Grind_AC_isIdempotent(
        v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_,
        v_a_4970_, v_a_4971_, v_a_4972_,
    );
    lean_dec(v_a_4972_);
    lean_dec_ref(v_a_4971_);
    lean_dec(v_a_4970_);
    lean_dec_ref(v_a_4969_);
    lean_dec(v_a_4968_);
    lean_dec_ref(v_a_4967_);
    lean_dec(v_a_4966_);
    lean_dec_ref(v_a_4965_);
    lean_dec(v_a_4964_);
    lean_dec(v_a_4963_);
    lean_dec(v_a_4962_);
    return v_res_4974_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc =
        _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc();
    lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
}

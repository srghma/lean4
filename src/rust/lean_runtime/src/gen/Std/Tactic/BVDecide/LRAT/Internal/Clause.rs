// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Clause
// Imports: Std.Data.HashMap Std.Sat.CNF.Basic Std.Tactic.BVDecide.LRAT.Internal.Assignment Init.Data.List.Erase Init.Data.List.Pairwise
use crate::r#gen::Init::Core::l_instBEqProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_any___redArg, l_List_elem___redArg, l_List_mapTR_loop___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::List::Erase::{
    initialize_Init_Data_List_Erase, runtime_initialize_Init_Data_List_Erase,
};
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_eraseTR_go;
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Basic::{
    l_instToStringBool___lam__0___boxed, l_instToStringProd___redArg___lam__0,
};
use crate::r#gen::Init::Data::ToString::Extra::l_List_toString___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqBool___boxed,
};
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
use crate::r#gen::Std::Sat::CNF::Basic::{
    initialize_Std_Sat_CNF_Basic, runtime_initialize_Std_Sat_CNF_Basic,
};
use crate::r#gen::Std::Sat::CNF::Literal::l_Std_Sat_Literal_negate;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Assignment::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::PosFin::l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3_value
) as *mut LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__3_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6_value
) as *mut LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__6_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__8_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10_value
) as *mut LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10_value) as *mut LeanObject,7213727686127018646 as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11_value
) as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14_value
) as *mut LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__14_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5_value) as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16_value
) as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0_value:
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
    m_fun: l_instToStringBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1_value:
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
    m_fun: l_Nat_reprFast as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2_value:
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
    m_fun: l_instToStringProd___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3_value:
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
    m_fun: l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0_value:
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
    m_fun: l_Std_Sat_Literal_negate as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg(
    mut v_x_789_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_789_) {
        0 => {
            let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
            v___x_790_ = lean_unsigned_to_nat(0);
            return v___x_790_;
        }
        1 => {
            let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
            v___x_791_ = lean_unsigned_to_nat(1);
            return v___x_791_;
        }
        2 => {
            let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
            v___x_792_ = lean_unsigned_to_nat(2);
            return v___x_792_;
        }
        _ => {
            let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
            v___x_793_ = lean_unsigned_to_nat(3);
            return v___x_793_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg___boxed(
    mut v_x_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_795_: *mut LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg(v_x_794_);
    lean_dec(v_x_794_);
    return v_res_795_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx(
    mut v_00_u03b1_796_: *mut LeanObject,
    mut v_x_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___redArg(v_x_797_);
    return v___x_798_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx___boxed(
    mut v_00_u03b1_799_: *mut LeanObject,
    mut v_x_800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_801_: *mut LeanObject = core::ptr::null_mut();
    v_res_801_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorIdx(v_00_u03b1_799_, v_x_800_);
    lean_dec(v_x_800_);
    return v_res_801_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
    mut v_t_802_: *mut LeanObject,
    mut v_k_803_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_802_) == 2 {
        let mut v_l_804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
        v_l_804_ = lean_ctor_get(v_t_802_, 0);
        lean_inc_ref(v_l_804_);
        lean_dec_ref_known(v_t_802_, 1);
        v___x_805_ = lean_apply_1(v_k_803_, v_l_804_);
        return v___x_805_;
    } else {
        lean_dec(v_t_802_);
        return v_k_803_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim(
    mut v_00_u03b1_806_: *mut LeanObject,
    mut v_motive_807_: *mut LeanObject,
    mut v_ctorIdx_808_: *mut LeanObject,
    mut v_t_809_: *mut LeanObject,
    mut v_h_810_: *mut LeanObject,
    mut v_k_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(v_t_809_, v_k_811_);
    return v___x_812_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___boxed(
    mut v_00_u03b1_813_: *mut LeanObject,
    mut v_motive_814_: *mut LeanObject,
    mut v_ctorIdx_815_: *mut LeanObject,
    mut v_t_816_: *mut LeanObject,
    mut v_h_817_: *mut LeanObject,
    mut v_k_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_819_: *mut LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim(
        v_00_u03b1_813_,
        v_motive_814_,
        v_ctorIdx_815_,
        v_t_816_,
        v_h_817_,
        v_k_818_,
    );
    lean_dec(v_ctorIdx_815_);
    return v_res_819_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_encounteredBoth_elim___redArg(
    mut v_t_820_: *mut LeanObject,
    mut v_encounteredBoth_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    v___x_822_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_820_,
        v_encounteredBoth_821_,
    );
    return v___x_822_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_encounteredBoth_elim(
    mut v_00_u03b1_823_: *mut LeanObject,
    mut v_motive_824_: *mut LeanObject,
    mut v_t_825_: *mut LeanObject,
    mut v_h_826_: *mut LeanObject,
    mut v_encounteredBoth_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_828_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_825_,
        v_encounteredBoth_827_,
    );
    return v___x_828_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToEmpty_elim___redArg(
    mut v_t_829_: *mut LeanObject,
    mut v_reducedToEmpty_830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_829_,
        v_reducedToEmpty_830_,
    );
    return v___x_831_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToEmpty_elim(
    mut v_00_u03b1_832_: *mut LeanObject,
    mut v_motive_833_: *mut LeanObject,
    mut v_t_834_: *mut LeanObject,
    mut v_h_835_: *mut LeanObject,
    mut v_reducedToEmpty_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_837_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_834_,
        v_reducedToEmpty_836_,
    );
    return v___x_837_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToUnit_elim___redArg(
    mut v_t_838_: *mut LeanObject,
    mut v_reducedToUnit_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_838_,
        v_reducedToUnit_839_,
    );
    return v___x_840_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToUnit_elim(
    mut v_00_u03b1_841_: *mut LeanObject,
    mut v_motive_842_: *mut LeanObject,
    mut v_t_843_: *mut LeanObject,
    mut v_h_844_: *mut LeanObject,
    mut v_reducedToUnit_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    v___x_846_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_843_,
        v_reducedToUnit_845_,
    );
    return v___x_846_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToNonunit_elim___redArg(
    mut v_t_847_: *mut LeanObject,
    mut v_reducedToNonunit_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_847_,
        v_reducedToNonunit_848_,
    );
    return v___x_849_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_reducedToNonunit_elim(
    mut v_00_u03b1_850_: *mut LeanObject,
    mut v_motive_851_: *mut LeanObject,
    mut v_t_852_: *mut LeanObject,
    mut v_h_853_: *mut LeanObject,
    mut v_reducedToNonunit_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Std_Tactic_BVDecide_LRAT_Internal_ReduceResult_ctorElim___redArg(
        v_t_852_,
        v_reducedToNonunit_854_,
    );
    return v___x_855_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntailsLiteral(
    mut v_00_u03b1_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    v___x_857_ = lean_box(0);
    return v___x_857_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(
    mut v_p_858_: *mut LeanObject,
    mut v_l_859_: *mut LeanObject,
) -> u8 {
    let mut v_fst_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: u8 = 0;
    v_fst_860_ = lean_ctor_get(v_l_859_, 0);
    lean_inc(v_fst_860_);
    v_snd_861_ = lean_ctor_get(v_l_859_, 1);
    lean_inc(v_snd_861_);
    lean_dec_ref(v_l_859_);
    v___x_862_ = lean_apply_1(v_p_858_, v_fst_860_);
    v___x_863_ = (lean_unbox(v___x_862_) as u8);
    if v___x_863_ == 0 {
        let mut v___x_864_: u8 = 0;
        v___x_864_ = (lean_unbox(v_snd_861_) as u8);
        lean_dec(v_snd_861_);
        if v___x_864_ == 0 {
            let mut v___x_865_: u8 = 0;
            v___x_865_ = 1;
            return v___x_865_;
        } else {
            let mut v___x_866_: u8 = 0;
            v___x_866_ = (lean_unbox(v___x_862_) as u8);
            return v___x_866_;
        }
    } else {
        let mut v___x_867_: u8 = 0;
        v___x_867_ = (lean_unbox(v_snd_861_) as u8);
        lean_dec(v_snd_861_);
        return v___x_867_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg___boxed(
    mut v_p_868_: *mut LeanObject,
    mut v_l_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_870_: u8 = 0;
    let mut v_r_871_: *mut LeanObject = core::ptr::null_mut();
    v_res_870_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(
        v_p_868_, v_l_869_,
    );
    v_r_871_ = lean_box((v_res_870_) as usize);
    return v_r_871_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral(
    mut v_00_u03b1_872_: *mut LeanObject,
    mut v_p_873_: *mut LeanObject,
    mut v_l_874_: *mut LeanObject,
) -> u8 {
    let mut v___x_875_: u8 = 0;
    v___x_875_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(
        v_p_873_, v_l_874_,
    );
    return v___x_875_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___boxed(
    mut v_00_u03b1_876_: *mut LeanObject,
    mut v_p_877_: *mut LeanObject,
    mut v_l_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_879_: u8 = 0;
    let mut v_r_880_: *mut LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral(
        v_00_u03b1_876_,
        v_p_877_,
        v_l_878_,
    );
    v_r_880_ = lean_box((v_res_879_) as usize);
    return v_r_880_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0(
    mut v_a_881_: *mut LeanObject,
    mut v_l_882_: *mut LeanObject,
) -> u8 {
    let mut v___x_883_: u8 = 0;
    v___x_883_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEvalLiteral___redArg(
        v_a_881_, v_l_882_,
    );
    return v___x_883_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0___boxed(
    mut v_a_884_: *mut LeanObject,
    mut v_l_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_886_: u8 = 0;
    let mut v_r_887_: *mut LeanObject = core::ptr::null_mut();
    v_res_886_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0(v_a_884_, v_l_885_);
    v_r_887_ = lean_box((v_res_886_) as usize);
    return v_r_887_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(
    mut v_inst_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
    mut v_c_890_: *mut LeanObject,
) -> u8 {
    let mut v_toList_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    v_toList_891_ = lean_ctor_get(v_inst_888_, 0);
    lean_inc_ref(v_toList_891_);
    lean_dec_ref(v_inst_888_);
    v___f_892_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_892_, 0, v_a_889_);
    v___x_893_ = lean_apply_1(v_toList_891_, v_c_890_);
    v___x_894_ = l_List_any___redArg(v___x_893_, v___f_892_);
    return v___x_894_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg___boxed(
    mut v_inst_895_: *mut LeanObject,
    mut v_a_896_: *mut LeanObject,
    mut v_c_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_898_: u8 = 0;
    let mut v_r_899_: *mut LeanObject = core::ptr::null_mut();
    v_res_898_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_895_, v_a_896_, v_c_897_);
    v_r_899_ = lean_box((v_res_898_) as usize);
    return v_r_899_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval(
    mut v_00_u03b1_900_: *mut LeanObject,
    mut v_00_u03b2_901_: *mut LeanObject,
    mut v_inst_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
    mut v_c_904_: *mut LeanObject,
) -> u8 {
    let mut v___x_905_: u8 = 0;
    v___x_905_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_902_, v_a_903_, v_c_904_);
    return v___x_905_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___boxed(
    mut v_00_u03b1_906_: *mut LeanObject,
    mut v_00_u03b2_907_: *mut LeanObject,
    mut v_inst_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
    mut v_c_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_911_: u8 = 0;
    let mut v_r_912_: *mut LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval(
        v_00_u03b1_906_,
        v_00_u03b2_907_,
        v_inst_908_,
        v_a_909_,
        v_c_910_,
    );
    v_r_912_ = lean_box((v_res_911_) as usize);
    return v_r_912_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails(
    mut v_00_u03b1_913_: *mut LeanObject,
    mut v_00_u03b2_914_: *mut LeanObject,
    mut v_inst_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    v___x_916_ = lean_box(0);
    return v___x_916_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails___boxed(
    mut v_00_u03b1_917_: *mut LeanObject,
    mut v_00_u03b2_918_: *mut LeanObject,
    mut v_inst_919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_920_: *mut LeanObject = core::ptr::null_mut();
    v_res_920_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instEntails(
        v_00_u03b1_917_,
        v_00_u03b2_918_,
        v_inst_919_,
    );
    lean_dec_ref(v_inst_919_);
    return v_res_920_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg(
    mut v_inst_921_: *mut LeanObject,
    mut v_p_922_: *mut LeanObject,
    mut v_c_923_: *mut LeanObject,
) -> u8 {
    let mut v___x_924_: u8 = 0;
    v___x_924_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_921_, v_p_922_, v_c_923_);
    return v___x_924_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg___boxed(
    mut v_inst_925_: *mut LeanObject,
    mut v_p_926_: *mut LeanObject,
    mut v_c_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_928_: u8 = 0;
    let mut v_r_929_: *mut LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___redArg(
        v_inst_925_,
        v_p_926_,
        v_c_927_,
    );
    v_r_929_ = lean_box((v_res_928_) as usize);
    return v_r_929_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval(
    mut v_00_u03b1_930_: *mut LeanObject,
    mut v_00_u03b2_931_: *mut LeanObject,
    mut v_inst_932_: *mut LeanObject,
    mut v_p_933_: *mut LeanObject,
    mut v_c_934_: *mut LeanObject,
) -> u8 {
    let mut v___x_935_: u8 = 0;
    v___x_935_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Clause_eval___redArg(v_inst_932_, v_p_933_, v_c_934_);
    return v___x_935_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval___boxed(
    mut v_00_u03b1_936_: *mut LeanObject,
    mut v_00_u03b2_937_: *mut LeanObject,
    mut v_inst_938_: *mut LeanObject,
    mut v_p_939_: *mut LeanObject,
    mut v_c_940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_941_: u8 = 0;
    let mut v_r_942_: *mut LeanObject = core::ptr::null_mut();
    v_res_941_ = l_Std_Tactic_BVDecide_LRAT_Internal_Clause_instDecidableEval(
        v_00_u03b1_936_,
        v_00_u03b2_937_,
        v_inst_938_,
        v_p_939_,
        v_c_940_,
    );
    v_r_942_ = lean_box((v_res_941_) as usize);
    return v_r_942_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12()
-> *mut LeanObject {
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v___x_969_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__10;
    v___x_970_ = l_Lean_mkAtom(v___x_969_);
    return v___x_970_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13()
-> *mut LeanObject {
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    v___x_971_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__12);
    v___x_972_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5;
    v___x_973_ = lean_array_push(v___x_972_, v___x_971_);
    return v___x_973_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17()
-> *mut LeanObject {
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    v___x_984_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16;
    v___x_985_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5;
    v___x_986_ = lean_array_push(v___x_985_, v___x_984_);
    return v___x_986_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18()
-> *mut LeanObject {
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    v___x_987_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__17);
    v___x_988_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__15;
    v___x_989_ = lean_box(2);
    v___x_990_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_990_, 0, v___x_989_);
    lean_ctor_set(v___x_990_, 1, v___x_988_);
    lean_ctor_set(v___x_990_, 2, v___x_987_);
    return v___x_990_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19()
-> *mut LeanObject {
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    v___x_991_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__18);
    v___x_992_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__13);
    v___x_993_ = lean_array_push(v___x_992_, v___x_991_);
    return v___x_993_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20()
-> *mut LeanObject {
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    v___x_994_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16;
    v___x_995_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__19);
    v___x_996_ = lean_array_push(v___x_995_, v___x_994_);
    return v___x_996_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21()
-> *mut LeanObject {
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    v___x_997_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16;
    v___x_998_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__20);
    v___x_999_ = lean_array_push(v___x_998_, v___x_997_);
    return v___x_999_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22()
-> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__16;
    v___x_1001_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__21);
    v___x_1002_ = lean_array_push(v___x_1001_, v___x_1000_);
    return v___x_1002_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23()
-> *mut LeanObject {
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1003_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__22);
    v___x_1004_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__11;
    v___x_1005_ = lean_box(2);
    v___x_1006_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1006_, 0, v___x_1005_);
    lean_ctor_set(v___x_1006_, 1, v___x_1004_);
    lean_ctor_set(v___x_1006_, 2, v___x_1003_);
    return v___x_1006_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24()
-> *mut LeanObject {
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1007_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__23);
    v___x_1008_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5;
    v___x_1009_ = lean_array_push(v___x_1008_, v___x_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25()
-> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__24);
    v___x_1011_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__9;
    v___x_1012_ = lean_box(2);
    v___x_1013_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1013_, 0, v___x_1012_);
    lean_ctor_set(v___x_1013_, 1, v___x_1011_);
    lean_ctor_set(v___x_1013_, 2, v___x_1010_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26()
-> *mut LeanObject {
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v___x_1014_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__25);
    v___x_1015_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5;
    v___x_1016_ = lean_array_push(v___x_1015_, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27()
-> *mut LeanObject {
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__26);
    v___x_1018_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__7;
    v___x_1019_ = lean_box(2);
    v___x_1020_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1020_, 0, v___x_1019_);
    lean_ctor_set(v___x_1020_, 1, v___x_1018_);
    lean_ctor_set(v___x_1020_, 2, v___x_1017_);
    return v___x_1020_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28()
-> *mut LeanObject {
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__27);
    v___x_1022_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__5;
    v___x_1023_ = lean_array_push(v___x_1022_, v___x_1021_);
    return v___x_1023_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29()
-> *mut LeanObject {
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v___x_1024_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__28);
    v___x_1025_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__4;
    v___x_1026_ = lean_box(2);
    v___x_1027_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    lean_ctor_set(v___x_1027_, 1, v___x_1025_);
    lean_ctor_set(v___x_1027_, 2, v___x_1024_);
    return v___x_1027_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam()
-> *mut LeanObject {
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    v___x_1028_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29);
    return v___x_1028_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam()
-> *mut LeanObject {
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    v___x_1029_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam___closed__29);
    return v___x_1029_;
}
pub unsafe fn l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(
    mut v_x_1030_: *mut LeanObject,
    mut v_x_1031_: *mut LeanObject,
) -> u8 {
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: u8 = 0;
    let mut v_head_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1040_: u8 = 0;
    let mut v_fst_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: u8 = 0;
    let mut v___x_1048_: u8 = 0;
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1030_) == 0 {
                    if lean_obj_tag(v_x_1031_) == 0 {
                        v___x_1032_ = 1;
                        return v___x_1032_;
                    } else {
                        v___x_1033_ = 0;
                        return v___x_1033_;
                    }
                } else {
                    if lean_obj_tag(v_x_1031_) == 0 {
                        v___x_1034_ = 0;
                        return v___x_1034_;
                    } else {
                        v_head_1035_ = lean_ctor_get(v_x_1030_, 0);
                        v_tail_1036_ = lean_ctor_get(v_x_1030_, 1);
                        v_head_1037_ = lean_ctor_get(v_x_1031_, 0);
                        v_tail_1038_ = lean_ctor_get(v_x_1031_, 1);
                        v_fst_1042_ = lean_ctor_get(v_head_1035_, 0);
                        v_snd_1043_ = lean_ctor_get(v_head_1035_, 1);
                        v_fst_1044_ = lean_ctor_get(v_head_1037_, 0);
                        v_snd_1045_ = lean_ctor_get(v_head_1037_, 1);
                        v___x_1046_ = lean_nat_dec_eq(v_fst_1042_, v_fst_1044_);
                        if v___x_1046_ == 0 {
                            v___y_1040_ = v___x_1046_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1047_ = (lean_unbox(v_snd_1043_) as u8);
                            if v___x_1047_ == 0 {
                                v___x_1048_ = (lean_unbox(v_snd_1045_) as u8);
                                if v___x_1048_ == 0 {
                                    v___y_1040_ = v___x_1046_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1049_ = (lean_unbox(v_snd_1043_) as u8);
                                    return v___x_1049_;
                                }
                            } else {
                                v___x_1050_ = (lean_unbox(v_snd_1045_) as u8);
                                v___y_1040_ = v___x_1050_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_1040_ == 0 {
                    return v___y_1040_;
                } else {
                    v_x_1030_ = v_tail_1036_;
                    v_x_1031_ = v_tail_1038_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg___boxed(
    mut v_x_1051_: *mut LeanObject,
    mut v_x_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1053_: u8 = 0;
    let mut v_r_1054_: *mut LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_x_1051_, v_x_1052_);
    lean_dec(v_x_1052_);
    lean_dec(v_x_1051_);
    v_r_1054_ = lean_box((v_res_1053_) as usize);
    return v_r_1054_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq(
    mut v_numVarsSucc_1055_: *mut LeanObject,
    mut v_x_1056_: *mut LeanObject,
    mut v_x_1057_: *mut LeanObject,
) -> u8 {
    let mut v___x_1058_: u8 = 0;
    v___x_1058_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_x_1056_, v_x_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq___boxed(
    mut v_numVarsSucc_1059_: *mut LeanObject,
    mut v_x_1060_: *mut LeanObject,
    mut v_x_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1062_: u8 = 0;
    let mut v_r_1063_: *mut LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq(
        v_numVarsSucc_1059_,
        v_x_1060_,
        v_x_1061_,
    );
    lean_dec(v_x_1061_);
    lean_dec(v_x_1060_);
    lean_dec(v_numVarsSucc_1059_);
    v_r_1063_ = lean_box((v_res_1062_) as usize);
    return v_r_1063_;
}
pub unsafe fn l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0(
    mut v_numVarsSucc_1064_: *mut LeanObject,
    mut v_x_1065_: *mut LeanObject,
    mut v_x_1066_: *mut LeanObject,
) -> u8 {
    let mut v___x_1067_: u8 = 0;
    v___x_1067_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_x_1065_, v_x_1066_);
    return v___x_1067_;
}
pub unsafe fn l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___boxed(
    mut v_numVarsSucc_1068_: *mut LeanObject,
    mut v_x_1069_: *mut LeanObject,
    mut v_x_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1071_: u8 = 0;
    let mut v_r_1072_: *mut LeanObject = core::ptr::null_mut();
    v_res_1071_ =
        l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0(
            v_numVarsSucc_1068_,
            v_x_1069_,
            v_x_1070_,
        );
    lean_dec(v_x_1070_);
    lean_dec(v_x_1069_);
    lean_dec(v_numVarsSucc_1068_);
    v_r_1072_ = lean_box((v_res_1071_) as usize);
    return v_r_1072_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause(
    mut v_numVarsSucc_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    v___x_1074_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_1074_, 0, v_numVarsSucc_1073_);
    return v___x_1074_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___lam__0(
    mut v___f_1075_: *mut LeanObject,
    mut v_c_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    v___x_1077_ = l_List_reverse___redArg(v_c_1076_);
    v___x_1078_ = l_List_toString___redArg(v___f_1075_, v___x_1077_);
    return v___x_1078_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause(
    mut v_n_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1087_: *mut LeanObject = core::ptr::null_mut();
    v___f_1087_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___closed__3;
    return v___f_1087_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause___boxed(
    mut v_n_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1089_: *mut LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringDefaultClause(v_n_1088_);
    lean_dec(v_n_1088_);
    return v_res_1089_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg(
    mut v_c_1090_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_c_1090_);
    return v_c_1090_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg___boxed(
    mut v_c_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___redArg(v_c_1091_);
    lean_dec(v_c_1091_);
    return v_res_1092_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList(
    mut v_n_1093_: *mut LeanObject,
    mut v_c_1094_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_c_1094_);
    return v_c_1094_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___boxed(
    mut v_n_1095_: *mut LeanObject,
    mut v_c_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1097_: *mut LeanObject = core::ptr::null_mut();
    v_res_1097_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList(v_n_1095_, v_c_1096_);
    lean_dec(v_c_1096_);
    lean_dec(v_n_1095_);
    return v_res_1097_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty(
    mut v_n_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    v___x_1099_ = lean_box(0);
    return v___x_1099_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty___boxed(
    mut v_n_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1101_: *mut LeanObject = core::ptr::null_mut();
    v_res_1101_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_empty(v_n_1100_);
    lean_dec(v_n_1100_);
    return v_res_1101_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___redArg(
    mut v_l_1102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    v___x_1103_ = lean_box(0);
    v___x_1104_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1104_, 0, v_l_1102_);
    lean_ctor_set(v___x_1104_, 1, v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit(
    mut v_n_1105_: *mut LeanObject,
    mut v_l_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = lean_box(0);
    v___x_1108_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1108_, 0, v_l_1106_);
    lean_ctor_set(v___x_1108_, 1, v___x_1107_);
    return v___x_1108_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___boxed(
    mut v_n_1109_: *mut LeanObject,
    mut v_l_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1111_: *mut LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit(v_n_1109_, v_l_1110_);
    lean_dec(v_n_1109_);
    return v_res_1111_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg(
    mut v_c_1112_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_c_1112_) == 1 {
        let mut v_tail_1113_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1113_ = lean_ctor_get(v_c_1112_, 1);
        if lean_obj_tag(v_tail_1113_) == 0 {
            let mut v_head_1114_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
            v_head_1114_ = lean_ctor_get(v_c_1112_, 0);
            lean_inc(v_head_1114_);
            v___x_1115_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1115_, 0, v_head_1114_);
            return v___x_1115_;
        } else {
            let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
            v___x_1116_ = lean_box(0);
            return v___x_1116_;
        }
    } else {
        let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
        v___x_1117_ = lean_box(0);
        return v___x_1117_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg___boxed(
    mut v_c_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1119_: *mut LeanObject = core::ptr::null_mut();
    v_res_1119_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___redArg(v_c_1118_);
    lean_dec(v_c_1118_);
    return v_res_1119_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit(
    mut v_n_1120_: *mut LeanObject,
    mut v_c_1121_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_c_1121_) == 1 {
        let mut v_tail_1122_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1122_ = lean_ctor_get(v_c_1121_, 1);
        if lean_obj_tag(v_tail_1122_) == 0 {
            let mut v_head_1123_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
            v_head_1123_ = lean_ctor_get(v_c_1121_, 0);
            lean_inc(v_head_1123_);
            v___x_1124_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1124_, 0, v_head_1123_);
            return v___x_1124_;
        } else {
            let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
            v___x_1125_ = lean_box(0);
            return v___x_1125_;
        }
    } else {
        let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
        v___x_1126_ = lean_box(0);
        return v___x_1126_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___boxed(
    mut v_n_1127_: *mut LeanObject,
    mut v_c_1128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1129_: *mut LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit(v_n_1127_, v_c_1128_);
    lean_dec(v_c_1128_);
    lean_dec(v_n_1127_);
    return v_res_1129_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter___redArg(
    mut v_x_1130_: *mut LeanObject,
    mut v_h__1_1131_: *mut LeanObject,
    mut v_h__2_1132_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1130_) == 1 {
        let mut v_tail_1133_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1133_ = lean_ctor_get(v_x_1130_, 1);
        if lean_obj_tag(v_tail_1133_) == 0 {
            let mut v_head_1134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1132_);
            v_head_1134_ = lean_ctor_get(v_x_1130_, 0);
            lean_inc(v_head_1134_);
            lean_dec_ref_known(v_x_1130_, 2);
            v___x_1135_ = lean_apply_1(v_h__1_1131_, v_head_1134_);
            return v___x_1135_;
        } else {
            let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1131_);
            v___x_1136_ = lean_apply_2(v_h__2_1132_, v_x_1130_, lean_box(0));
            return v___x_1136_;
        }
    } else {
        let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1131_);
        v___x_1137_ = lean_apply_2(v_h__2_1132_, v_x_1130_, lean_box(0));
        return v___x_1137_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter(
    mut v_n_1138_: *mut LeanObject,
    mut v_motive_1139_: *mut LeanObject,
    mut v_x_1140_: *mut LeanObject,
    mut v_h__1_1141_: *mut LeanObject,
    mut v_h__2_1142_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1140_) == 1 {
        let mut v_tail_1143_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1143_ = lean_ctor_get(v_x_1140_, 1);
        if lean_obj_tag(v_tail_1143_) == 0 {
            let mut v_head_1144_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1142_);
            v_head_1144_ = lean_ctor_get(v_x_1140_, 0);
            lean_inc(v_head_1144_);
            lean_dec_ref_known(v_x_1140_, 2);
            v___x_1145_ = lean_apply_1(v_h__1_1141_, v_head_1144_);
            return v___x_1145_;
        } else {
            let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1141_);
            v___x_1146_ = lean_apply_2(v_h__2_1142_, v_x_1140_, lean_box(0));
            return v___x_1146_;
        }
    } else {
        let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1141_);
        v___x_1147_ = lean_apply_2(v_h__2_1142_, v_x_1140_, lean_box(0));
        return v___x_1147_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter___boxed(
    mut v_n_1148_: *mut LeanObject,
    mut v_motive_1149_: *mut LeanObject,
    mut v_x_1150_: *mut LeanObject,
    mut v_h__1_1151_: *mut LeanObject,
    mut v_h__2_1152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1153_: *mut LeanObject = core::ptr::null_mut();
    v_res_1153_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit_match__1_splitter(v_n_1148_, v_motive_1149_, v_x_1150_, v_h__1_1151_, v_h__2_1152_);
    lean_dec(v_n_1148_);
    return v_res_1153_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg(
    mut v_c_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0;
    v___x_1157_ = lean_box(0);
    v___x_1158_ = l_List_mapTR_loop___redArg(v___x_1156_, v_c_1155_, v___x_1157_);
    return v___x_1158_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate(
    mut v_n_1159_: *mut LeanObject,
    mut v_c_1160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___redArg___closed__0;
    v___x_1162_ = lean_box(0);
    v___x_1163_ = l_List_mapTR_loop___redArg(v___x_1161_, v_c_1160_, v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___boxed(
    mut v_n_1164_: *mut LeanObject,
    mut v_c_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1166_: *mut LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate(v_n_1164_, v_c_1165_);
    lean_dec(v_n_1164_);
    return v_res_1166_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(
    mut v_a_1167_: *mut LeanObject,
    mut v_x_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: u8 = 0;
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1168_) == 0 {
                    v___x_1169_ = lean_box(0);
                    return v___x_1169_;
                } else {
                    v_key_1170_ = lean_ctor_get(v_x_1168_, 0);
                    v_value_1171_ = lean_ctor_get(v_x_1168_, 1);
                    v_tail_1172_ = lean_ctor_get(v_x_1168_, 2);
                    v___x_1173_ = lean_nat_dec_eq(v_key_1170_, v_a_1167_);
                    if v___x_1173_ == 0 {
                        v_x_1168_ = v_tail_1172_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1171_);
                        v___x_1175_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1175_, 0, v_value_1171_);
                        return v___x_1175_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg___boxed(
    mut v_a_1176_: *mut LeanObject,
    mut v_x_1177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1178_: *mut LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_a_1176_, v_x_1177_);
    lean_dec(v_x_1177_);
    lean_dec(v_a_1176_);
    return v_res_1178_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(
    mut v_x_1179_: *mut LeanObject,
    mut v_x_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u64 = 0;
    let mut v___x_1189_: u64 = 0;
    let mut v___x_1190_: u64 = 0;
    let mut v_fold_1191_: u64 = 0;
    let mut v___x_1192_: u64 = 0;
    let mut v___x_1193_: u64 = 0;
    let mut v___x_1194_: u64 = 0;
    let mut v___x_1195_: usize = 0;
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1180_) == 0 {
                    return v_x_1179_;
                } else {
                    v_key_1181_ = lean_ctor_get(v_x_1180_, 0);
                    v_value_1182_ = lean_ctor_get(v_x_1180_, 1);
                    v_tail_1183_ = lean_ctor_get(v_x_1180_, 2);
                    v_isSharedCheck_1206_ = (!lean_is_exclusive(v_x_1180_)) as u8;
                    if v_isSharedCheck_1206_ == 0 {
                        v___x_1185_ = v_x_1180_;
                        v_isShared_1186_ = v_isSharedCheck_1206_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1183_);
                        lean_inc(v_value_1182_);
                        lean_inc(v_key_1181_);
                        lean_dec(v_x_1180_);
                        v___x_1185_ = lean_box(0);
                        v_isShared_1186_ = v_isSharedCheck_1206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1187_ = lean_array_get_size(v_x_1179_);
                v___x_1188_ = lean_uint64_of_nat(v_key_1181_);
                v___x_1189_ = 32u64;
                v___x_1190_ = lean_uint64_shift_right(v___x_1188_, v___x_1189_);
                v_fold_1191_ = lean_uint64_xor(v___x_1188_, v___x_1190_);
                v___x_1192_ = 16u64;
                v___x_1193_ = lean_uint64_shift_right(v_fold_1191_, v___x_1192_);
                v___x_1194_ = lean_uint64_xor(v_fold_1191_, v___x_1193_);
                v___x_1195_ = lean_uint64_to_usize(v___x_1194_);
                v___x_1196_ = lean_usize_of_nat(v___x_1187_);
                v___x_1197_ = 1usize;
                v___x_1198_ = lean_usize_sub(v___x_1196_, v___x_1197_);
                v___x_1199_ = lean_usize_land(v___x_1195_, v___x_1198_);
                v___x_1200_ = lean_array_uget_borrowed(v_x_1179_, v___x_1199_);
                lean_inc(v___x_1200_);
                if v_isShared_1186_ == 0 {
                    lean_ctor_set(v___x_1185_, 2, v___x_1200_);
                    v___x_1202_ = v___x_1185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_key_1181_);
                    lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_value_1182_);
                    lean_ctor_set(v_reuseFailAlloc_1205_, 2, v___x_1200_);
                    v___x_1202_ = v_reuseFailAlloc_1205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1203_ = lean_array_uset(v_x_1179_, v___x_1199_, v___x_1202_);
                v_x_1179_ = v___x_1203_;
                v_x_1180_ = v_tail_1183_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(
    mut v_i_1207_: *mut LeanObject,
    mut v_source_1208_: *mut LeanObject,
    mut v_target_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: u8 = 0;
    let mut v_es_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1210_ = lean_array_get_size(v_source_1208_);
                v___x_1211_ = lean_nat_dec_lt(v_i_1207_, v___x_1210_);
                if v___x_1211_ == 0 {
                    lean_dec_ref(v_source_1208_);
                    lean_dec(v_i_1207_);
                    return v_target_1209_;
                } else {
                    v_es_1212_ = lean_array_fget(v_source_1208_, v_i_1207_);
                    v___x_1213_ = lean_box(0);
                    v_source_1214_ = lean_array_fset(v_source_1208_, v_i_1207_, v___x_1213_);
                    v_target_1215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(v_target_1209_, v_es_1212_);
                    v___x_1216_ = lean_unsigned_to_nat(1);
                    v___x_1217_ = lean_nat_add(v_i_1207_, v___x_1216_);
                    lean_dec(v_i_1207_);
                    v_i_1207_ = v___x_1217_;
                    v_source_1208_ = v_source_1214_;
                    v_target_1209_ = v_target_1215_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(
    mut v_n_1219_: *mut LeanObject,
    mut v_data_1220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = lean_array_get_size(v_data_1220_);
    v___x_1222_ = lean_unsigned_to_nat(2);
    v_nbuckets_1223_ = lean_nat_mul(v___x_1221_, v___x_1222_);
    v___x_1224_ = lean_unsigned_to_nat(0);
    v___x_1225_ = lean_box(0);
    v___x_1226_ = lean_mk_array(v_nbuckets_1223_, v___x_1225_);
    v___x_1227_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(v___x_1224_, v_data_1220_, v___x_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg___boxed(
    mut v_n_1228_: *mut LeanObject,
    mut v_data_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1230_: *mut LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_1228_, v_data_1229_);
    lean_dec(v_n_1228_);
    return v_res_1230_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(
    mut v_n_1231_: *mut LeanObject,
    mut v_acc_1232_: *mut LeanObject,
    mut v_l_1233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v_size_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u8 = 0;
    let mut v_val_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1249_: u8 = 0;
    let mut v___x_1250_: u8 = 0;
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut v_val_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u64 = 0;
    let mut v___x_1271_: u64 = 0;
    let mut v___x_1272_: u64 = 0;
    let mut v_fold_1273_: u64 = 0;
    let mut v___x_1274_: u64 = 0;
    let mut v___x_1275_: u64 = 0;
    let mut v___x_1276_: u64 = 0;
    let mut v___x_1277_: usize = 0;
    let mut v___x_1278_: usize = 0;
    let mut v___x_1279_: usize = 0;
    let mut v___x_1280_: usize = 0;
    let mut v___x_1281_: usize = 0;
    let mut v_bkt_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: u8 = 0;
    let mut v_val_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_unused_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_acc_1232_) == 0 {
                    return v_acc_1232_;
                } else {
                    v_val_1234_ = lean_ctor_get(v_acc_1232_, 0);
                    v_isSharedCheck_1307_ = (!lean_is_exclusive(v_acc_1232_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1236_ = v_acc_1232_;
                        v_isShared_1237_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1234_);
                        lean_dec(v_acc_1232_);
                        v___x_1236_ = lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_size_1238_ = lean_ctor_get(v_val_1234_, 0);
                v_buckets_1239_ = lean_ctor_get(v_val_1234_, 1);
                v_fst_1240_ = lean_ctor_get(v_l_1233_, 0);
                v_snd_1241_ = lean_ctor_get(v_l_1233_, 1);
                v___x_1269_ = lean_array_get_size(v_buckets_1239_);
                v___x_1270_ = lean_uint64_of_nat(v_fst_1240_);
                v___x_1271_ = 32u64;
                v___x_1272_ = lean_uint64_shift_right(v___x_1270_, v___x_1271_);
                v_fold_1273_ = lean_uint64_xor(v___x_1270_, v___x_1272_);
                v___x_1274_ = 16u64;
                v___x_1275_ = lean_uint64_shift_right(v_fold_1273_, v___x_1274_);
                v___x_1276_ = lean_uint64_xor(v_fold_1273_, v___x_1275_);
                v___x_1277_ = lean_uint64_to_usize(v___x_1276_);
                v___x_1278_ = lean_usize_of_nat(v___x_1269_);
                v___x_1279_ = 1usize;
                v___x_1280_ = lean_usize_sub(v___x_1278_, v___x_1279_);
                v___x_1281_ = lean_usize_land(v___x_1277_, v___x_1280_);
                v_bkt_1282_ = lean_array_uget_borrowed(v_buckets_1239_, v___x_1281_);
                v___x_1283_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_fst_1240_, v_bkt_1282_);
                if lean_obj_tag(v___x_1283_) == 0 {
                    lean_inc_ref(v_buckets_1239_);
                    lean_inc(v_size_1238_);
                    v_isSharedCheck_1304_ = (!lean_is_exclusive(v_val_1234_)) as u8;
                    if v_isSharedCheck_1304_ == 0 {
                        v_unused_1305_ = lean_ctor_get(v_val_1234_, 1);
                        lean_dec(v_unused_1305_);
                        v_unused_1306_ = lean_ctor_get(v_val_1234_, 0);
                        lean_dec(v_unused_1306_);
                        v___x_1285_ = v_val_1234_;
                        v_isShared_1286_ = v_isSharedCheck_1304_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_val_1234_);
                        v___x_1285_ = lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1304_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_fst_1243_ = v___x_1283_;
                    v_snd_1244_ = v_val_1234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v_fst_1243_) == 1 {
                    lean_del_object(v___x_1236_);
                    v___x_1245_ = (lean_unbox(v_snd_1241_) as u8);
                    if v___x_1245_ == 0 {
                        v_val_1246_ = lean_ctor_get(v_fst_1243_, 0);
                        v_isSharedCheck_1255_ = (!lean_is_exclusive(v_fst_1243_)) as u8;
                        if v_isSharedCheck_1255_ == 0 {
                            v___x_1248_ = v_fst_1243_;
                            v_isShared_1249_ = v_isSharedCheck_1255_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_1246_);
                            lean_dec(v_fst_1243_);
                            v___x_1248_ = lean_box(0);
                            v_isShared_1249_ = v_isSharedCheck_1255_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_val_1256_ = lean_ctor_get(v_fst_1243_, 0);
                        v_isSharedCheck_1265_ = (!lean_is_exclusive(v_fst_1243_)) as u8;
                        if v_isSharedCheck_1265_ == 0 {
                            v___x_1258_ = v_fst_1243_;
                            v_isShared_1259_ = v_isSharedCheck_1265_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_val_1256_);
                            lean_dec(v_fst_1243_);
                            v___x_1258_ = lean_box(0);
                            v_isShared_1259_ = v_isSharedCheck_1265_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_1243_);
                    if v_isShared_1237_ == 0 {
                        lean_ctor_set(v___x_1236_, 0, v_snd_1244_);
                        v___x_1267_ = v___x_1236_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_snd_1244_);
                        v___x_1267_ = v_reuseFailAlloc_1268_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1250_ = (lean_unbox(v_val_1246_) as u8);
                lean_dec(v_val_1246_);
                if v___x_1250_ == 0 {
                    if v_isShared_1249_ == 0 {
                        lean_ctor_set(v___x_1248_, 0, v_snd_1244_);
                        v___x_1252_ = v___x_1248_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_snd_1244_);
                        v___x_1252_ = v_reuseFailAlloc_1253_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1248_);
                    lean_dec(v_snd_1244_);
                    v___x_1254_ = lean_box(0);
                    return v___x_1254_;
                }
            }
            4 => {
                return v___x_1252_;
            }
            5 => {
                v___x_1260_ = (lean_unbox(v_val_1256_) as u8);
                lean_dec(v_val_1256_);
                if v___x_1260_ == 0 {
                    lean_del_object(v___x_1258_);
                    lean_dec(v_snd_1244_);
                    v___x_1261_ = lean_box(0);
                    return v___x_1261_;
                } else {
                    if v_isShared_1259_ == 0 {
                        lean_ctor_set(v___x_1258_, 0, v_snd_1244_);
                        v___x_1263_ = v___x_1258_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_snd_1244_);
                        v___x_1263_ = v_reuseFailAlloc_1264_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1263_;
            }
            7 => {
                return v___x_1267_;
            }
            8 => {
                v___x_1287_ = lean_unsigned_to_nat(1);
                v_size_x27_1288_ = lean_nat_add(v_size_1238_, v___x_1287_);
                lean_dec(v_size_1238_);
                lean_inc(v_bkt_1282_);
                lean_inc(v_snd_1241_);
                lean_inc(v_fst_1240_);
                v___x_1289_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1289_, 0, v_fst_1240_);
                lean_ctor_set(v___x_1289_, 1, v_snd_1241_);
                lean_ctor_set(v___x_1289_, 2, v_bkt_1282_);
                v_buckets_x27_1290_ = lean_array_uset(v_buckets_1239_, v___x_1281_, v___x_1289_);
                v___x_1291_ = lean_unsigned_to_nat(4);
                v___x_1292_ = lean_nat_mul(v_size_x27_1288_, v___x_1291_);
                v___x_1293_ = lean_unsigned_to_nat(3);
                v___x_1294_ = lean_nat_div(v___x_1292_, v___x_1293_);
                lean_dec(v___x_1292_);
                v___x_1295_ = lean_array_get_size(v_buckets_x27_1290_);
                v___x_1296_ = lean_nat_dec_le(v___x_1294_, v___x_1295_);
                lean_dec(v___x_1294_);
                if v___x_1296_ == 0 {
                    v_val_1297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_1231_, v_buckets_x27_1290_);
                    if v_isShared_1286_ == 0 {
                        lean_ctor_set(v___x_1285_, 1, v_val_1297_);
                        lean_ctor_set(v___x_1285_, 0, v_size_x27_1288_);
                        v___x_1299_ = v___x_1285_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_size_x27_1288_);
                        lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_val_1297_);
                        v___x_1299_ = v_reuseFailAlloc_1300_;
                        state = 9;
                        continue;
                    }
                } else {
                    if v_isShared_1286_ == 0 {
                        lean_ctor_set(v___x_1285_, 1, v_buckets_x27_1290_);
                        lean_ctor_set(v___x_1285_, 0, v_size_x27_1288_);
                        v___x_1302_ = v___x_1285_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_size_x27_1288_);
                        lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_buckets_x27_1290_);
                        v___x_1302_ = v_reuseFailAlloc_1303_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                v_fst_1243_ = v___x_1283_;
                v_snd_1244_ = v___x_1299_;
                state = 2;
                continue;
            }
            10 => {
                v_fst_1243_ = v___x_1283_;
                v_snd_1244_ = v___x_1302_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder___boxed(
    mut v_n_1308_: *mut LeanObject,
    mut v_acc_1309_: *mut LeanObject,
    mut v_l_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1311_: *mut LeanObject = core::ptr::null_mut();
    v_res_1311_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(
        v_n_1308_,
        v_acc_1309_,
        v_l_1310_,
    );
    lean_dec_ref(v_l_1310_);
    lean_dec(v_n_1308_);
    return v_res_1311_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(
    mut v_n_1312_: *mut LeanObject,
    mut v_00_u03b2_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
    mut v_x_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___redArg(v_a_1314_, v_x_1315_);
    return v___x_1316_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0___boxed(
    mut v_n_1317_: *mut LeanObject,
    mut v_00_u03b2_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
    mut v_x_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1321_: *mut LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__0(v_n_1317_, v_00_u03b2_1318_, v_a_1319_, v_x_1320_);
    lean_dec(v_x_1320_);
    lean_dec(v_a_1319_);
    lean_dec(v_n_1317_);
    return v_res_1321_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(
    mut v_n_1322_: *mut LeanObject,
    mut v_00_u03b2_1323_: *mut LeanObject,
    mut v_data_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___redArg(v_n_1322_, v_data_1324_);
    return v___x_1325_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1___boxed(
    mut v_n_1326_: *mut LeanObject,
    mut v_00_u03b2_1327_: *mut LeanObject,
    mut v_data_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1329_: *mut LeanObject = core::ptr::null_mut();
    v_res_1329_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1(v_n_1326_, v_00_u03b2_1327_, v_data_1328_);
    lean_dec(v_n_1326_);
    return v_res_1329_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1(
    mut v_n_1330_: *mut LeanObject,
    mut v_00_u03b2_1331_: *mut LeanObject,
    mut v_i_1332_: *mut LeanObject,
    mut v_source_1333_: *mut LeanObject,
    mut v_target_1334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___redArg(v_i_1332_, v_source_1333_, v_target_1334_);
    return v___x_1335_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1___boxed(
    mut v_n_1336_: *mut LeanObject,
    mut v_00_u03b2_1337_: *mut LeanObject,
    mut v_i_1338_: *mut LeanObject,
    mut v_source_1339_: *mut LeanObject,
    mut v_target_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1341_: *mut LeanObject = core::ptr::null_mut();
    v_res_1341_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1(v_n_1336_, v_00_u03b2_1337_, v_i_1338_, v_source_1339_, v_target_1340_);
    lean_dec(v_n_1336_);
    return v_res_1341_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1342_: *mut LeanObject,
    mut v_x_1343_: *mut LeanObject,
    mut v_x_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_spec__1_spec__1_spec__2___redArg(v_x_1343_, v_x_1344_);
    return v___x_1345_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(
    mut v_acc_1346_: *mut LeanObject,
    mut v_h__1_1347_: *mut LeanObject,
    mut v_h__2_1348_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_acc_1346_) == 0 {
        let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1348_);
        v___x_1349_ = lean_box(0);
        v___x_1350_ = lean_apply_1(v_h__1_1347_, v___x_1349_);
        return v___x_1350_;
    } else {
        let mut v_val_1351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1347_);
        v_val_1351_ = lean_ctor_get(v_acc_1346_, 0);
        lean_inc(v_val_1351_);
        lean_dec_ref_known(v_acc_1346_, 1);
        v___x_1352_ = lean_apply_1(v_h__2_1348_, v_val_1351_);
        return v___x_1352_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(
    mut v_n_1353_: *mut LeanObject,
    mut v_motive_1354_: *mut LeanObject,
    mut v_acc_1355_: *mut LeanObject,
    mut v_h__1_1356_: *mut LeanObject,
    mut v_h__2_1357_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_acc_1355_) == 0 {
        let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1357_);
        v___x_1358_ = lean_box(0);
        v___x_1359_ = lean_apply_1(v_h__1_1356_, v___x_1358_);
        return v___x_1359_;
    } else {
        let mut v_val_1360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1356_);
        v_val_1360_ = lean_ctor_get(v_acc_1355_, 0);
        lean_inc(v_val_1360_);
        lean_dec_ref_known(v_acc_1355_, 1);
        v___x_1361_ = lean_apply_1(v_h__2_1357_, v_val_1360_);
        return v___x_1361_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(
    mut v_n_1362_: *mut LeanObject,
    mut v_motive_1363_: *mut LeanObject,
    mut v_acc_1364_: *mut LeanObject,
    mut v_h__1_1365_: *mut LeanObject,
    mut v_h__2_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1367_: *mut LeanObject = core::ptr::null_mut();
    v_res_1367_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(v_n_1362_, v_motive_1363_, v_acc_1364_, v_h__1_1365_, v_h__2_1366_);
    lean_dec(v_n_1362_);
    return v_res_1367_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(
    mut v_x_1368_: *mut LeanObject,
    mut v_x_1369_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1369_) == 0 {
        lean_inc(v_x_1368_);
        return v_x_1368_;
    } else {
        let mut v_key_1370_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1371_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
        v_key_1370_ = lean_ctor_get(v_x_1369_, 0);
        v_value_1371_ = lean_ctor_get(v_x_1369_, 1);
        v_tail_1372_ = lean_ctor_get(v_x_1369_, 2);
        v___x_1373_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_x_1368_, v_tail_1372_);
        lean_inc(v_value_1371_);
        lean_inc(v_key_1370_);
        v___x_1374_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1374_, 0, v_key_1370_);
        lean_ctor_set(v___x_1374_, 1, v_value_1371_);
        v___x_1375_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1375_, 0, v___x_1374_);
        lean_ctor_set(v___x_1375_, 1, v___x_1373_);
        return v___x_1375_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0___boxed(
    mut v_x_1376_: *mut LeanObject,
    mut v_x_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1378_: *mut LeanObject = core::ptr::null_mut();
    v_res_1378_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_x_1376_, v_x_1377_);
    lean_dec(v_x_1377_);
    lean_dec(v_x_1376_);
    return v_res_1378_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(
    mut v_as_1379_: *mut LeanObject,
    mut v_i_1380_: usize,
    mut v_stop_1381_: usize,
    mut v_b_1382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: usize = 0;
    let mut v___x_1385_: usize = 0;
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1383_ = lean_usize_dec_eq(v_i_1380_, v_stop_1381_);
                if v___x_1383_ == 0 {
                    v___x_1384_ = 1usize;
                    v___x_1385_ = lean_usize_sub(v_i_1380_, v___x_1384_);
                    v___x_1386_ = lean_array_uget_borrowed(v_as_1379_, v___x_1385_);
                    v___x_1387_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__0(v_b_1382_, v___x_1386_);
                    lean_dec(v_b_1382_);
                    v_i_1380_ = v___x_1385_;
                    v_b_1382_ = v___x_1387_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1382_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1___boxed(
    mut v_as_1389_: *mut LeanObject,
    mut v_i_1390_: *mut LeanObject,
    mut v_stop_1391_: *mut LeanObject,
    mut v_b_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1393_: usize = 0;
    let mut v_stop_boxed_1394_: usize = 0;
    let mut v_res_1395_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1393_ = lean_unbox_usize(v_i_1390_);
    lean_dec(v_i_1390_);
    v_stop_boxed_1394_ = lean_unbox_usize(v_stop_1391_);
    lean_dec(v_stop_1391_);
    v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_as_1389_, v_i_boxed_1393_, v_stop_boxed_1394_, v_b_1392_);
    lean_dec_ref(v_as_1389_);
    return v_res_1395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(
    mut v_n_1396_: *mut LeanObject,
    mut v_as_1397_: *mut LeanObject,
    mut v_i_1398_: usize,
    mut v_stop_1399_: usize,
    mut v_b_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1401_ = lean_usize_dec_eq(v_i_1398_, v_stop_1399_);
                if v___x_1401_ == 0 {
                    v___x_1402_ = lean_array_uget_borrowed(v_as_1397_, v_i_1398_);
                    v___x_1403_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder(
                        v_n_1396_,
                        v_b_1400_,
                        v___x_1402_,
                    );
                    v___x_1404_ = 1usize;
                    v___x_1405_ = lean_usize_add(v_i_1398_, v___x_1404_);
                    v_i_1398_ = v___x_1405_;
                    v_b_1400_ = v___x_1403_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1400_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2___boxed(
    mut v_n_1407_: *mut LeanObject,
    mut v_as_1408_: *mut LeanObject,
    mut v_i_1409_: *mut LeanObject,
    mut v_stop_1410_: *mut LeanObject,
    mut v_b_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1412_: usize = 0;
    let mut v_stop_boxed_1413_: usize = 0;
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1412_ = lean_unbox_usize(v_i_1409_);
    lean_dec(v_i_1409_);
    v_stop_boxed_1413_ = lean_unbox_usize(v_stop_1410_);
    lean_dec(v_stop_1410_);
    v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_1407_, v_as_1408_, v_i_boxed_1412_, v_stop_boxed_1413_, v_b_1411_);
    lean_dec_ref(v_as_1408_);
    lean_dec(v_n_1407_);
    return v_res_1414_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(
    mut v_n_1417_: *mut LeanObject,
    mut v_ls_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: usize = 0;
    let mut v___x_1427_: usize = 0;
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: usize = 0;
    let mut v___x_1452_: usize = 0;
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1435_ = lean_array_get_size(v_ls_1418_);
                v___x_1436_ = lean_unsigned_to_nat(0);
                v___x_1437_ = lean_unsigned_to_nat(4);
                v___x_1438_ = lean_nat_mul(v___x_1435_, v___x_1437_);
                v___x_1439_ = lean_unsigned_to_nat(3);
                v___x_1440_ = lean_nat_div(v___x_1438_, v___x_1439_);
                lean_dec(v___x_1438_);
                v___x_1441_ = l_Nat_nextPowerOfTwo(v___x_1440_);
                lean_dec(v___x_1440_);
                v___x_1442_ = lean_box(0);
                v___x_1443_ = lean_mk_array(v___x_1441_, v___x_1442_);
                v___x_1444_ = lean_nat_dec_lt(v___x_1436_, v___x_1435_);
                if v___x_1444_ == 0 {
                    v_buckets_1420_ = v___x_1443_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v___x_1443_);
                    v___x_1445_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1445_, 0, v___x_1436_);
                    lean_ctor_set(v___x_1445_, 1, v___x_1443_);
                    v___x_1446_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1446_, 0, v___x_1445_);
                    v___x_1447_ = lean_nat_dec_le(v___x_1435_, v___x_1435_);
                    if v___x_1447_ == 0 {
                        if v___x_1444_ == 0 {
                            lean_dec_ref_known(v___x_1446_, 1);
                            v_buckets_1420_ = v___x_1443_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___x_1443_);
                            v___x_1448_ = 0usize;
                            v___x_1449_ = lean_usize_of_nat(v___x_1435_);
                            v___x_1450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_1417_, v_ls_1418_, v___x_1448_, v___x_1449_, v___x_1446_);
                            v___y_1431_ = v___x_1450_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1443_);
                        v___x_1451_ = 0usize;
                        v___x_1452_ = lean_usize_of_nat(v___x_1435_);
                        v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__2(v_n_1417_, v_ls_1418_, v___x_1451_, v___x_1452_, v___x_1446_);
                        v___y_1431_ = v___x_1453_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1421_ = lean_box(0);
                v___x_1422_ = lean_array_get_size(v_buckets_1420_);
                v___x_1423_ = lean_unsigned_to_nat(0);
                v___x_1424_ = lean_nat_dec_lt(v___x_1423_, v___x_1422_);
                if v___x_1424_ == 0 {
                    lean_dec_ref(v_buckets_1420_);
                    v___x_1425_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___closed__0;
                    return v___x_1425_;
                } else {
                    v___x_1426_ = lean_usize_of_nat(v___x_1422_);
                    v___x_1427_ = 0usize;
                    v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_spec__1(v_buckets_1420_, v___x_1426_, v___x_1427_, v___x_1421_);
                    lean_dec_ref(v_buckets_1420_);
                    v___x_1429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1429_, 0, v___x_1428_);
                    return v___x_1429_;
                }
            }
            2 => {
                if lean_obj_tag(v___y_1431_) == 0 {
                    v___x_1432_ = lean_box(0);
                    return v___x_1432_;
                } else {
                    v_val_1433_ = lean_ctor_get(v___y_1431_, 0);
                    lean_inc(v_val_1433_);
                    lean_dec_ref_known(v___y_1431_, 1);
                    v_buckets_1434_ = lean_ctor_get(v_val_1433_, 1);
                    lean_inc_ref(v_buckets_1434_);
                    lean_dec(v_val_1433_);
                    v_buckets_1420_ = v_buckets_1434_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed(
    mut v_n_1454_: *mut LeanObject,
    mut v_ls_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_1454_, v_ls_1455_);
    lean_dec_ref(v_ls_1455_);
    lean_dec(v_n_1454_);
    return v_res_1456_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter___redArg(
    mut v_val_x3f_1457_: *mut LeanObject,
    mut v_h__1_1458_: *mut LeanObject,
    mut v_h__2_1459_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_val_x3f_1457_) == 1 {
        let mut v_val_1460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1459_);
        v_val_1460_ = lean_ctor_get(v_val_x3f_1457_, 0);
        lean_inc(v_val_1460_);
        lean_dec_ref_known(v_val_x3f_1457_, 1);
        v___x_1461_ = lean_apply_1(v_h__1_1458_, v_val_1460_);
        return v___x_1461_;
    } else {
        let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1458_);
        v___x_1462_ = lean_apply_2(v_h__2_1459_, v_val_x3f_1457_, lean_box(0));
        return v___x_1462_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Clause_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__1_splitter(
    mut v_motive_1463_: *mut LeanObject,
    mut v_val_x3f_1464_: *mut LeanObject,
    mut v_h__1_1465_: *mut LeanObject,
    mut v_h__2_1466_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_val_x3f_1464_) == 1 {
        let mut v_val_1467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1466_);
        v_val_1467_ = lean_ctor_get(v_val_x3f_1464_, 0);
        lean_inc(v_val_1467_);
        lean_dec_ref_known(v_val_x3f_1464_, 1);
        v___x_1468_ = lean_apply_1(v_h__1_1465_, v_val_1467_);
        return v___x_1468_;
    } else {
        let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1465_);
        v___x_1469_ = lean_apply_2(v_h__2_1466_, v_val_x3f_1464_, lean_box(0));
        return v___x_1469_;
    }
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0()
-> *mut LeanObject {
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1471_: *mut LeanObject = core::ptr::null_mut();
    v___x_1470_ = lean_alloc_closure(
        l_instDecidableEqBool___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1471_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1471_, 0, v___x_1470_);
    return v___f_1471_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete(
    mut v_n_1474_: *mut LeanObject,
    mut v_c_1475_: *mut LeanObject,
    mut v_l_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    v___x_1477_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_1477_, 0, v_n_1474_);
    v___f_1478_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1478_, 0, v___x_1477_);
    v___f_1479_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0,
    );
    v___f_1480_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1480_, 0, v___f_1478_);
    lean_closure_set(v___f_1480_, 1, v___f_1479_);
    v___x_1481_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__1;
    lean_inc(v_c_1475_);
    v___x_1482_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(
        lean_box(0),
        v___f_1480_,
        v_c_1475_,
        v_l_1476_,
        v_c_1475_,
        v___x_1481_,
    );
    lean_dec(v_c_1475_);
    return v___x_1482_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(
    mut v_n_1483_: *mut LeanObject,
    mut v_c_1484_: *mut LeanObject,
    mut v_l_1485_: *mut LeanObject,
) -> u8 {
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    v___x_1486_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_1486_, 0, v_n_1483_);
    v___f_1487_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1487_, 0, v___x_1486_);
    v___f_1488_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete___closed__0,
    );
    v___f_1489_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1489_, 0, v___f_1487_);
    lean_closure_set(v___f_1489_, 1, v___f_1488_);
    v___x_1490_ = l_List_elem___redArg(v___f_1489_, v_l_1485_, v_c_1484_);
    return v___x_1490_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed(
    mut v_n_1491_: *mut LeanObject,
    mut v_c_1492_: *mut LeanObject,
    mut v_l_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1494_: u8 = 0;
    let mut v_r_1495_: *mut LeanObject = core::ptr::null_mut();
    v_res_1494_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains(v_n_1491_, v_c_1492_, v_l_1493_);
    v_r_1495_ = lean_box((v_res_1494_) as usize);
    return v_r_1495_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(
    mut v_assignments_1496_: *mut LeanObject,
    mut v_acc_1497_: *mut LeanObject,
    mut v_l_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1499_: u8 = 0;
    v___x_1499_ = 0;
    match lean_obj_tag(v_acc_1497_) {
        1 => {
            let mut v_fst_1500_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1501_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1504_: u8 = 0;
            v_fst_1500_ = lean_ctor_get(v_l_1498_, 0);
            v_snd_1501_ = lean_ctor_get(v_l_1498_, 1);
            v___x_1502_ = lean_box((v___x_1499_) as usize);
            v___x_1503_ = lean_array_get(v___x_1502_, v_assignments_1496_, v_fst_1500_);
            lean_dec(v___x_1502_);
            v___x_1504_ = (lean_unbox(v___x_1503_) as u8);
            lean_dec(v___x_1503_);
            match v___x_1504_ {
                0 => {
                    let mut v___x_1505_: u8 = 0;
                    v___x_1505_ = (lean_unbox(v_snd_1501_) as u8);
                    if v___x_1505_ == 0 {
                        lean_dec_ref(v_l_1498_);
                        return v_acc_1497_;
                    } else {
                        let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1506_ = lean_alloc_ctor(2, 1, (0) as u32);
                        lean_ctor_set(v___x_1506_, 0, v_l_1498_);
                        return v___x_1506_;
                    }
                }
                1 => {
                    let mut v___x_1507_: u8 = 0;
                    v___x_1507_ = (lean_unbox(v_snd_1501_) as u8);
                    if v___x_1507_ == 0 {
                        let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1508_ = lean_alloc_ctor(2, 1, (0) as u32);
                        lean_ctor_set(v___x_1508_, 0, v_l_1498_);
                        return v___x_1508_;
                    } else {
                        lean_dec_ref(v_l_1498_);
                        return v_acc_1497_;
                    }
                }
                2 => {
                    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_l_1498_);
                    v___x_1509_ = lean_box(0);
                    return v___x_1509_;
                }
                _ => {
                    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
                    v___x_1510_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_1510_, 0, v_l_1498_);
                    return v___x_1510_;
                }
            }
        }
        2 => {
            let mut v_fst_1511_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1512_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1515_: u8 = 0;
            v_fst_1511_ = lean_ctor_get(v_l_1498_, 0);
            lean_inc(v_fst_1511_);
            v_snd_1512_ = lean_ctor_get(v_l_1498_, 1);
            lean_inc(v_snd_1512_);
            lean_dec_ref(v_l_1498_);
            v___x_1513_ = lean_box((v___x_1499_) as usize);
            v___x_1514_ = lean_array_get(v___x_1513_, v_assignments_1496_, v_fst_1511_);
            lean_dec(v_fst_1511_);
            lean_dec(v___x_1513_);
            v___x_1515_ = (lean_unbox(v___x_1514_) as u8);
            lean_dec(v___x_1514_);
            match v___x_1515_ {
                0 => {
                    let mut v___x_1516_: u8 = 0;
                    v___x_1516_ = (lean_unbox(v_snd_1512_) as u8);
                    lean_dec(v_snd_1512_);
                    if v___x_1516_ == 0 {
                        lean_inc_ref(v_acc_1497_);
                        return v_acc_1497_;
                    } else {
                        let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1517_ = lean_box(3);
                        return v___x_1517_;
                    }
                }
                1 => {
                    let mut v___x_1518_: u8 = 0;
                    v___x_1518_ = (lean_unbox(v_snd_1512_) as u8);
                    lean_dec(v_snd_1512_);
                    if v___x_1518_ == 0 {
                        let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1519_ = lean_box(3);
                        return v___x_1519_;
                    } else {
                        lean_inc_ref(v_acc_1497_);
                        return v_acc_1497_;
                    }
                }
                2 => {
                    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_snd_1512_);
                    v___x_1520_ = lean_box(0);
                    return v___x_1520_;
                }
                _ => {
                    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_snd_1512_);
                    v___x_1521_ = lean_box(3);
                    return v___x_1521_;
                }
            }
        }
        _ => {
            lean_dec_ref(v_l_1498_);
            lean_inc(v_acc_1497_);
            return v_acc_1497_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg___boxed(
    mut v_assignments_1522_: *mut LeanObject,
    mut v_acc_1523_: *mut LeanObject,
    mut v_l_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(
        v_assignments_1522_,
        v_acc_1523_,
        v_l_1524_,
    );
    lean_dec(v_acc_1523_);
    lean_dec_ref(v_assignments_1522_);
    return v_res_1525_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(
    mut v_n_1526_: *mut LeanObject,
    mut v_assignments_1527_: *mut LeanObject,
    mut v_acc_1528_: *mut LeanObject,
    mut v_l_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(
        v_assignments_1527_,
        v_acc_1528_,
        v_l_1529_,
    );
    return v___x_1530_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___boxed(
    mut v_n_1531_: *mut LeanObject,
    mut v_assignments_1532_: *mut LeanObject,
    mut v_acc_1533_: *mut LeanObject,
    mut v_l_1534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1535_: *mut LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn(
        v_n_1531_,
        v_assignments_1532_,
        v_acc_1533_,
        v_l_1534_,
    );
    lean_dec(v_acc_1533_);
    lean_dec_ref(v_assignments_1532_);
    lean_dec(v_n_1531_);
    return v_res_1535_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(
    mut v_assignments_1536_: *mut LeanObject,
    mut v_x_1537_: *mut LeanObject,
    mut v_x_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1538_) == 0 {
                    return v_x_1537_;
                } else {
                    v_head_1539_ = lean_ctor_get(v_x_1538_, 0);
                    lean_inc(v_head_1539_);
                    v_tail_1540_ = lean_ctor_get(v_x_1538_, 1);
                    lean_inc(v_tail_1540_);
                    lean_dec_ref_known(v_x_1538_, 2);
                    v___x_1541_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn___redArg(
                            v_assignments_1536_,
                            v_x_1537_,
                            v_head_1539_,
                        );
                    lean_dec(v_x_1537_);
                    v_x_1537_ = v___x_1541_;
                    v_x_1538_ = v_tail_1540_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg___boxed(
    mut v_assignments_1543_: *mut LeanObject,
    mut v_x_1544_: *mut LeanObject,
    mut v_x_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1546_: *mut LeanObject = core::ptr::null_mut();
    v_res_1546_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_1543_, v_x_1544_, v_x_1545_);
    lean_dec_ref(v_assignments_1543_);
    return v_res_1546_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(
    mut v_n_1547_: *mut LeanObject,
    mut v_c_1548_: *mut LeanObject,
    mut v_assignments_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1550_ = lean_box(1);
    v___x_1551_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_1549_, v___x_1550_, v_c_1548_);
    return v___x_1551_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed(
    mut v_n_1552_: *mut LeanObject,
    mut v_c_1553_: *mut LeanObject,
    mut v_assignments_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(
        v_n_1552_,
        v_c_1553_,
        v_assignments_1554_,
    );
    lean_dec_ref(v_assignments_1554_);
    lean_dec(v_n_1552_);
    return v_res_1555_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(
    mut v_n_1556_: *mut LeanObject,
    mut v_assignments_1557_: *mut LeanObject,
    mut v_x_1558_: *mut LeanObject,
    mut v_x_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___redArg(v_assignments_1557_, v_x_1558_, v_x_1559_);
    return v___x_1560_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0___boxed(
    mut v_n_1561_: *mut LeanObject,
    mut v_assignments_1562_: *mut LeanObject,
    mut v_x_1563_: *mut LeanObject,
    mut v_x_1564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1565_: *mut LeanObject = core::ptr::null_mut();
    v_res_1565_ =
        l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce_spec__0(
            v_n_1561_,
            v_assignments_1562_,
            v_x_1563_,
            v_x_1564_,
        );
    lean_dec_ref(v_assignments_1562_);
    lean_dec(v_n_1561_);
    return v_res_1565_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_instClausePosFin(
    mut v_n_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_n_1566_, 7);
    v___x_1567_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_toList___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_1567_, 0, v_n_1566_);
    v___x_1568_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_1568_, 0, v_n_1566_);
    v___x_1569_ = lean_box(0);
    v___x_1570_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_unit___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_1570_, 0, v_n_1566_);
    v___x_1571_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_isUnit___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_1571_, 0, v_n_1566_);
    v___x_1572_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_negate___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_1572_, 0, v_n_1566_);
    v___x_1573_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_delete as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_1573_, 0, v_n_1566_);
    v___x_1574_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_contains___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_1574_, 0, v_n_1566_);
    v___x_1575_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_1575_, 0, v_n_1566_);
    v___x_1576_ = lean_alloc_ctor(0, 9, (0) as u32);
    lean_ctor_set(v___x_1576_, 0, v___x_1567_);
    lean_ctor_set(v___x_1576_, 1, v___x_1568_);
    lean_ctor_set(v___x_1576_, 2, v___x_1569_);
    lean_ctor_set(v___x_1576_, 3, v___x_1570_);
    lean_ctor_set(v___x_1576_, 4, v___x_1571_);
    lean_ctor_set(v___x_1576_, 5, v___x_1572_);
    lean_ctor_set(v___x_1576_, 6, v___x_1573_);
    lean_ctor_set(v___x_1576_, 7, v___x_1574_);
    lean_ctor_set(v___x_1576_, 8, v___x_1575_);
    return v___x_1576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam();
    lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodupkey___autoParam);
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam();
    lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_nodup___autoParam);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_CNF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
}

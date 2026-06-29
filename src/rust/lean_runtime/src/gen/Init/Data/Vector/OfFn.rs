// Lean compiler output
// Module: Init.Data.Vector.OfFn
// Imports: Init.Data.Vector.Basic Init.Data.Array.OfFn Init.Data.Vector.Basic Init.Data.Fin.Lemmas Init.Data.Vector.Monadic Init.TacticsExtra
use crate::r#gen::Init::Data::Array::OfFn::{
    initialize_Init_Data_Array_OfFn, runtime_initialize_Init_Data_Array_OfFn,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Data::Vector::Monadic::{
    initialize_Init_Data_Vector_Monadic, runtime_initialize_Init_Data_Vector_Monadic,
};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__3_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__6_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__8_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 109, 101, 103, 97, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10_value) as *mut crate::leanh::LeanObject,14893461734720614794 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14_value
) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__14_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed(
    mut v_i_130_: *mut crate::leanh::LeanObject,
    mut v_acc_131_: *mut crate::leanh::LeanObject,
    mut v_n_132_: *mut crate::leanh::LeanObject,
    mut v_inst_133_: *mut crate::leanh::LeanObject,
    mut v_f_134_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_136_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(
        v_i_130_,
        v_acc_131_,
        v_n_132_,
        v_inst_133_,
        v_f_134_,
        v_____do__lift_135_,
    );
    crate::leanh::lean_dec(v_i_130_);
    return v_res_136_;
}
pub unsafe fn l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(
    mut v_n_137_: *mut crate::leanh::LeanObject,
    mut v_inst_138_: *mut crate::leanh::LeanObject,
    mut v_f_139_: *mut crate::leanh::LeanObject,
    mut v_i_140_: *mut crate::leanh::LeanObject,
    mut v_acc_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_142_: u8 = 0;
    v___x_142_ = lean_nat_dec_lt(v_i_140_, v_n_137_);
    if v___x_142_ == 0 {
        let mut v_toApplicative_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_140_);
        crate::leanh::lean_dec(v_f_139_);
        crate::leanh::lean_dec(v_n_137_);
        v_toApplicative_143_ = crate::leanh::lean_ctor_get(v_inst_138_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_143_);
        crate::leanh::lean_dec_ref(v_inst_138_);
        v_toPure_144_ = crate::leanh::lean_ctor_get(v_toApplicative_143_, 1);
        crate::leanh::lean_inc(v_toPure_144_);
        crate::leanh::lean_dec_ref(v_toApplicative_143_);
        v___x_145_ =
            crate::leanh::lean_apply_2(v_toPure_144_, crate::leanh::lean_box(0), v_acc_141_);
        return v___x_145_;
    } else {
        let mut v_toBind_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_146_ = crate::leanh::lean_ctor_get(v_inst_138_, 1);
        crate::leanh::lean_inc(v_toBind_146_);
        crate::leanh::lean_inc(v_f_139_);
        crate::leanh::lean_inc(v_i_140_);
        v___f_147_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_147_, 0, v_i_140_);
        crate::leanh::lean_closure_set(v___f_147_, 1, v_acc_141_);
        crate::leanh::lean_closure_set(v___f_147_, 2, v_n_137_);
        crate::leanh::lean_closure_set(v___f_147_, 3, v_inst_138_);
        crate::leanh::lean_closure_set(v___f_147_, 4, v_f_139_);
        v___x_148_ = crate::leanh::lean_apply_1(v_f_139_, v_i_140_);
        v___x_149_ = crate::leanh::lean_apply_4(
            v_toBind_146_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_148_,
            v___f_147_,
        );
        return v___x_149_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg___lam__0(
    mut v_i_150_: *mut crate::leanh::LeanObject,
    mut v_acc_151_: *mut crate::leanh::LeanObject,
    mut v_n_152_: *mut crate::leanh::LeanObject,
    mut v_inst_153_: *mut crate::leanh::LeanObject,
    mut v_f_154_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_157_ = lean_nat_add(v_i_150_, v___x_156_);
    v___x_158_ = lean_array_push(v_acc_151_, v_____do__lift_155_);
    v___x_159_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(
        v_n_152_,
        v_inst_153_,
        v_f_154_,
        v___x_157_,
        v___x_158_,
    );
    return v___x_159_;
}
pub unsafe fn l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go(
    mut v_m_160_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_161_: *mut crate::leanh::LeanObject,
    mut v_n_162_: *mut crate::leanh::LeanObject,
    mut v_inst_163_: *mut crate::leanh::LeanObject,
    mut v_f_164_: *mut crate::leanh::LeanObject,
    mut v_i_165_: *mut crate::leanh::LeanObject,
    mut v_h_x27_166_: *mut crate::leanh::LeanObject,
    mut v_acc_167_: *mut crate::leanh::LeanObject,
    mut v_w_168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_169_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(
        v_n_162_,
        v_inst_163_,
        v_f_164_,
        v_i_165_,
        v_acc_167_,
    );
    return v___x_169_;
}
pub unsafe fn l_Vector_ofFnM___redArg(
    mut v_n_170_: *mut crate::leanh::LeanObject,
    mut v_inst_171_: *mut crate::leanh::LeanObject,
    mut v_f_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_173_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_174_ = lean_mk_empty_array_with_capacity(v_n_170_);
    v___x_175_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM_go___redArg(
        v_n_170_,
        v_inst_171_,
        v_f_172_,
        v___x_173_,
        v___x_174_,
    );
    return v___x_175_;
}
pub unsafe fn l_Vector_ofFnM(
    mut v_m_176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_177_: *mut crate::leanh::LeanObject,
    mut v_n_178_: *mut crate::leanh::LeanObject,
    mut v_inst_179_: *mut crate::leanh::LeanObject,
    mut v_f_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_181_ = l_Vector_ofFnM___redArg(v_n_178_, v_inst_179_, v_f_180_);
    return v___x_181_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__10;
    v___x_209_ = l_Lean_mkAtom(v___x_208_);
    return v___x_209_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__12,
    );
    v___x_211_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5;
    v___x_212_ = lean_array_push(v___x_211_, v___x_210_);
    return v___x_212_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_223_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__16;
    v___x_224_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5;
    v___x_225_ = lean_array_push(v___x_224_, v___x_223_);
    return v___x_225_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_226_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__17,
    );
    v___x_227_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__15;
    v___x_228_ = crate::leanh::lean_box(2);
    v___x_229_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_229_, 0, v___x_228_);
    crate::leanh::lean_ctor_set(v___x_229_, 1, v___x_227_);
    crate::leanh::lean_ctor_set(v___x_229_, 2, v___x_226_);
    return v___x_229_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__18,
    );
    v___x_231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__13,
    );
    v___x_232_ = lean_array_push(v___x_231_, v___x_230_);
    return v___x_232_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_233_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__19,
    );
    v___x_234_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__11;
    v___x_235_ = crate::leanh::lean_box(2);
    v___x_236_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_236_, 0, v___x_235_);
    crate::leanh::lean_ctor_set(v___x_236_, 1, v___x_234_);
    crate::leanh::lean_ctor_set(v___x_236_, 2, v___x_233_);
    return v___x_236_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_237_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__20,
    );
    v___x_238_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5;
    v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
    return v___x_239_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__21,
    );
    v___x_241_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__9;
    v___x_242_ = crate::leanh::lean_box(2);
    v___x_243_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_243_, 0, v___x_242_);
    crate::leanh::lean_ctor_set(v___x_243_, 1, v___x_241_);
    crate::leanh::lean_ctor_set(v___x_243_, 2, v___x_240_);
    return v___x_243_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__22,
    );
    v___x_245_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5;
    v___x_246_ = lean_array_push(v___x_245_, v___x_244_);
    return v___x_246_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__23,
    );
    v___x_248_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__7;
    v___x_249_ = crate::leanh::lean_box(2);
    v___x_250_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_250_, 0, v___x_249_);
    crate::leanh::lean_ctor_set(v___x_250_, 1, v___x_248_);
    crate::leanh::lean_ctor_set(v___x_250_, 2, v___x_247_);
    return v___x_250_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__24,
    );
    v___x_252_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__5;
    v___x_253_ = lean_array_push(v___x_252_, v___x_251_);
    return v___x_253_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_254_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__25,
    );
    v___x_255_ = l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__4;
    v___x_256_ = crate::leanh::lean_box(2);
    v___x_257_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_257_, 0, v___x_256_);
    crate::leanh::lean_ctor_set(v___x_257_, 1, v___x_255_);
    crate::leanh::lean_ctor_set(v___x_257_, 2, v___x_254_);
    return v___x_257_;
}
pub unsafe fn _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26_once
        ),
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5___closed__26,
    );
    return v___x_258_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_OfFn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_OfFn(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5 =
        _init_l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5();
    crate::leanh::lean_mark_persistent(
        l___private_Init_Data_Vector_OfFn_0__Vector_ofFnM__go__succ___auto__5,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_OfFn(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_OfFn(builtin);
}

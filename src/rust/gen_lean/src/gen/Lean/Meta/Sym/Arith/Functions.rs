// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Functions
// Imports: Lean.Meta.Sym.Arith.MonadRing Lean.Meta.Sym.Arith.MonadSemiring
use crate::ffi::{
    lean_st_ref_get, lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Nat_mkType, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppB,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::Sym::Arith::MonadCanon::l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg;
use crate::r#gen::Lean::Meta::Sym::Arith::MonadRing::{
    initialize_Lean_Meta_Sym_Arith_MonadRing, runtime_initialize_Lean_Meta_Sym_Arith_MonadRing,
};
use crate::r#gen::Lean::Meta::Sym::Arith::MonadSemiring::{
    initialize_Lean_Meta_Sym_Arith_MonadSemiring,
    runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring,
};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [101, 114, 114, 111, 114, 32, 119, 104, 105, 108, 101, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 105, 110, 103, 32, 97, 114, 105, 116, 104, 109, 101, 116, 105, 99, 32, 111, 112, 101, 114, 97, 116, 111, 114, 115, 58, 10, 105, 110, 115, 116, 97, 110, 99, 101, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 32, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_value: crate::leanh::LeanStringObject<59> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 59, m_capacity: 59, m_length: 58, m_data: [10, 119, 104, 101, 110, 32, 111, 110, 108, 121, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 97, 114, 101, 32, 114, 101, 100, 117, 99, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject,18388652353510661091 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value) as *mut crate::leanh::LeanObject,14765357657372582228 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value) as *mut crate::leanh::LeanObject,5779414593499529281 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9594062259507646949 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 111, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5442360487226035463 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value)
            as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value)
            as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value)
            as *mut crate::leanh::LeanObject,
        10680564408669940870 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18134279130838690737 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 111, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7102027102192867304 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value)
            as *mut crate::leanh::LeanObject,
        1611444129324655608 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10135981711945425184 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [82, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 111, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18169824201013588232 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value)
            as *mut crate::leanh::LeanObject,
        16856108565602861689 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value)
            as *mut crate::leanh::LeanObject,
        16856108565602861689 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value)
            as *mut crate::leanh::LeanObject,
        4187025665268973031 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 111, 78, 101, 103, 0],
};
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10040236838748678500 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value)
            as *mut crate::leanh::LeanObject,
        17185717442815859305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value)
            as *mut crate::leanh::LeanObject,
        439118677539554485 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14561037289535094017 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [73, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4977321555018234431 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 105, 101, 108, 100, 0],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 111, 73, 110, 118, 0],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8615353994042975301 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7723290638220826725 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 118, 0],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value)
            as *mut crate::leanh::LeanObject,
        1412621069384631438 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 110, 118, 0],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value)
            as *mut crate::leanh::LeanObject,
        1412621069384631438 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value)
            as *mut crate::leanh::LeanObject,
        10171450186735820607 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 116, 121, 112,
        101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 102, 105, 101, 108, 100, 0,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(
    mut v_msgData_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = lean_st_ref_get(v___y_1460_);
    v_env_1463_ = crate::leanh::lean_ctor_get(v___x_1462_, 0);
    crate::leanh::lean_inc_ref(v_env_1463_);
    crate::leanh::lean_dec(v___x_1462_);
    v___x_1464_ = lean_st_ref_get(v___y_1458_);
    v_mctx_1465_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1465_);
    crate::leanh::lean_dec(v___x_1464_);
    v_lctx_1466_ = crate::leanh::lean_ctor_get(v___y_1457_, 2);
    v_options_1467_ = crate::leanh::lean_ctor_get(v___y_1459_, 2);
    crate::leanh::lean_inc_ref(v_options_1467_);
    crate::leanh::lean_inc_ref(v_lctx_1466_);
    v___x_1468_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1468_, 0, v_env_1463_);
    crate::leanh::lean_ctor_set(v___x_1468_, 1, v_mctx_1465_);
    crate::leanh::lean_ctor_set(v___x_1468_, 2, v_lctx_1466_);
    crate::leanh::lean_ctor_set(v___x_1468_, 3, v_options_1467_);
    v___x_1469_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1468_);
    crate::leanh::lean_ctor_set(v___x_1469_, 1, v_msgData_1456_);
    v___x_1470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1470_, 0, v___x_1469_);
    return v___x_1470_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(
    mut v_msgData_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msgData_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
    crate::leanh::lean_dec(v___y_1475_);
    crate::leanh::lean_dec_ref(v___y_1474_);
    crate::leanh::lean_dec(v___y_1473_);
    crate::leanh::lean_dec_ref(v___y_1472_);
    return v_res_1477_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(
    mut v_msg_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1489_: u8 = 0;
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1484_ = crate::leanh::lean_ctor_get(v___y_1481_, 5);
                v___x_1485_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
                v_a_1486_ = crate::leanh::lean_ctor_get(v___x_1485_, 0);
                v_isSharedCheck_1494_ = (!crate::leanh::lean_is_exclusive(v___x_1485_)) as u8;
                if v_isSharedCheck_1494_ == 0 {
                    v___x_1488_ = v___x_1485_;
                    v_isShared_1489_ = v_isSharedCheck_1494_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1486_);
                    crate::leanh::lean_dec(v___x_1485_);
                    v___x_1488_ = crate::leanh::lean_box(0);
                    v_isShared_1489_ = v_isSharedCheck_1494_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1484_);
                v___x_1490_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1490_, 0, v_ref_1484_);
                crate::leanh::lean_ctor_set(v___x_1490_, 1, v_a_1486_);
                if v_isShared_1489_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1488_, 1);
                    crate::leanh::lean_ctor_set(v___x_1488_, 0, v___x_1490_);
                    v___x_1492_ = v___x_1488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg___boxed(
    mut v_msg_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v___y_1497_);
    crate::leanh::lean_dec_ref(v___y_1496_);
    return v_res_1501_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0()
-> u64 {
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: u64 = 0;
    v___x_1502_ = 3;
    v___x_1503_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1502_);
    return v___x_1503_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1;
    v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3;
    v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
    return v___x_1509_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5;
    v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
    return v___x_1512_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7;
    v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
    return v___x_1515_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(
    mut v_declName_1516_: *mut crate::leanh::LeanObject,
    mut v_inst_1517_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_1518_: *mut crate::leanh::LeanObject,
    mut v_a_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
    mut v_a_1521_: *mut crate::leanh::LeanObject,
    mut v_a_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1525_: u8 = 0;
    let mut v_ctxApprox_1526_: u8 = 0;
    let mut v_quasiPatternApprox_1527_: u8 = 0;
    let mut v_constApprox_1528_: u8 = 0;
    let mut v_isDefEqStuckEx_1529_: u8 = 0;
    let mut v_unificationHints_1530_: u8 = 0;
    let mut v_proofIrrelevance_1531_: u8 = 0;
    let mut v_assignSyntheticOpaque_1532_: u8 = 0;
    let mut v_offsetCnstrs_1533_: u8 = 0;
    let mut v_etaStruct_1534_: u8 = 0;
    let mut v_univApprox_1535_: u8 = 0;
    let mut v_iota_1536_: u8 = 0;
    let mut v_beta_1537_: u8 = 0;
    let mut v_proj_1538_: u8 = 0;
    let mut v_zeta_1539_: u8 = 0;
    let mut v_zetaDelta_1540_: u8 = 0;
    let mut v_zetaUnused_1541_: u8 = 0;
    let mut v_zetaHave_1542_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1545_: u8 = 0;
    let mut v_trackZetaDelta_1546_: u8 = 0;
    let mut v_zetaDeltaSet_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1553_: u8 = 0;
    let mut v_inTypeClassResolution_1554_: u8 = 0;
    let mut v_cacheInferType_1555_: u8 = 0;
    let mut v___x_1556_: u8 = 0;
    let mut v_config_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u64 = 0;
    let mut v___x_1560_: u64 = 0;
    let mut v___x_1561_: u64 = 0;
    let mut v___x_1562_: u64 = 0;
    let mut v___x_1563_: u64 = 0;
    let mut v_key_1564_: u64 = 0;
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1572_: u8 = 0;
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_a_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_reuseFailAlloc_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1524_ = l_Lean_Meta_Context_config(v_a_1519_);
                v_foApprox_1525_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 0 as u32);
                v_ctxApprox_1526_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 1 as u32);
                v_quasiPatternApprox_1527_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1524_, 2 as u32);
                v_constApprox_1528_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 3 as u32);
                v_isDefEqStuckEx_1529_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 4 as u32);
                v_unificationHints_1530_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 5 as u32);
                v_proofIrrelevance_1531_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 6 as u32);
                v_assignSyntheticOpaque_1532_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1524_, 7 as u32);
                v_offsetCnstrs_1533_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 8 as u32);
                v_etaStruct_1534_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 10 as u32);
                v_univApprox_1535_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 11 as u32);
                v_iota_1536_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 12 as u32);
                v_beta_1537_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 13 as u32);
                v_proj_1538_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 14 as u32);
                v_zeta_1539_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 15 as u32);
                v_zetaDelta_1540_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 16 as u32);
                v_zetaUnused_1541_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 17 as u32);
                v_zetaHave_1542_ = crate::leanh::lean_ctor_get_uint8(v___x_1524_, 18 as u32);
                v_isSharedCheck_1601_ = (!crate::leanh::lean_is_exclusive(v___x_1524_)) as u8;
                if v_isSharedCheck_1601_ == 0 {
                    v___x_1544_ = v___x_1524_;
                    v_isShared_1545_ = v_isSharedCheck_1601_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1524_);
                    v___x_1544_ = crate::leanh::lean_box(0);
                    v_isShared_1545_ = v_isSharedCheck_1601_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_1546_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1547_ = crate::leanh::lean_ctor_get(v_a_1519_, 1);
                v_lctx_1548_ = crate::leanh::lean_ctor_get(v_a_1519_, 2);
                v_localInstances_1549_ = crate::leanh::lean_ctor_get(v_a_1519_, 3);
                v_defEqCtx_x3f_1550_ = crate::leanh::lean_ctor_get(v_a_1519_, 4);
                v_synthPendingDepth_1551_ = crate::leanh::lean_ctor_get(v_a_1519_, 5);
                v_canUnfold_x3f_1552_ = crate::leanh::lean_ctor_get(v_a_1519_, 6);
                v_univApprox_1553_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1554_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1555_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1556_ = 3;
                if v_isShared_1545_ == 0 {
                    v_config_1558_ = v___x_1544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        0 as u32,
                        v_foApprox_1525_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        1 as u32,
                        v_ctxApprox_1526_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        2 as u32,
                        v_quasiPatternApprox_1527_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        3 as u32,
                        v_constApprox_1528_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        4 as u32,
                        v_isDefEqStuckEx_1529_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        5 as u32,
                        v_unificationHints_1530_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        6 as u32,
                        v_proofIrrelevance_1531_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        7 as u32,
                        v_assignSyntheticOpaque_1532_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        8 as u32,
                        v_offsetCnstrs_1533_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        10 as u32,
                        v_etaStruct_1534_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        11 as u32,
                        v_univApprox_1535_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        12 as u32,
                        v_iota_1536_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        13 as u32,
                        v_beta_1537_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        14 as u32,
                        v_proj_1538_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        15 as u32,
                        v_zeta_1539_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        16 as u32,
                        v_zetaDelta_1540_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        17 as u32,
                        v_zetaUnused_1541_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        18 as u32,
                        v_zetaHave_1542_,
                    );
                    v_config_1558_ = v_reuseFailAlloc_1600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_1558_, 9 as u32, v___x_1556_);
                v___x_1559_ = l_Lean_Meta_Context_configKey(v_a_1519_);
                v___x_1560_ = 3u64;
                v___x_1561_ = lean_uint64_shift_right(v___x_1559_, v___x_1560_);
                v___x_1562_ = lean_uint64_shift_left(v___x_1561_, v___x_1560_);
                v___x_1563_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0);
                v_key_1564_ = lean_uint64_lor(v___x_1562_, v___x_1563_);
                v___x_1565_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1565_, 0, v_config_1558_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1565_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_1564_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1552_);
                crate::leanh::lean_inc(v_synthPendingDepth_1551_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1550_);
                crate::leanh::lean_inc_ref(v_localInstances_1549_);
                crate::leanh::lean_inc_ref(v_lctx_1548_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1547_);
                v___x_1566_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1566_, 0, v___x_1565_);
                crate::leanh::lean_ctor_set(v___x_1566_, 1, v_zetaDeltaSet_1547_);
                crate::leanh::lean_ctor_set(v___x_1566_, 2, v_lctx_1548_);
                crate::leanh::lean_ctor_set(v___x_1566_, 3, v_localInstances_1549_);
                crate::leanh::lean_ctor_set(v___x_1566_, 4, v_defEqCtx_x3f_1550_);
                crate::leanh::lean_ctor_set(v___x_1566_, 5, v_synthPendingDepth_1551_);
                crate::leanh::lean_ctor_set(v___x_1566_, 6, v_canUnfold_x3f_1552_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1546_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1553_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1554_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1555_,
                );
                crate::leanh::lean_inc_ref(v_inst_x27_1518_);
                crate::leanh::lean_inc_ref(v_inst_1517_);
                v___x_1567_ = l_Lean_Meta_isExprDefEq(
                    v_inst_1517_,
                    v_inst_x27_1518_,
                    v___x_1566_,
                    v_a_1520_,
                    v_a_1521_,
                    v_a_1522_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1566_, 7);
                if crate::leanh::lean_obj_tag(v___x_1567_) == 0 {
                    v_a_1568_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                    v_isSharedCheck_1591_ = (!crate::leanh::lean_is_exclusive(v___x_1567_)) as u8;
                    if v_isSharedCheck_1591_ == 0 {
                        v___x_1570_ = v___x_1567_;
                        v_isShared_1571_ = v_isSharedCheck_1591_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1568_);
                        crate::leanh::lean_dec(v___x_1567_);
                        v___x_1570_ = crate::leanh::lean_box(0);
                        v_isShared_1571_ = v_isSharedCheck_1591_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_x27_1518_);
                    crate::leanh::lean_dec_ref(v_inst_1517_);
                    crate::leanh::lean_dec(v_declName_1516_);
                    v_a_1592_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                    v_isSharedCheck_1599_ = (!crate::leanh::lean_is_exclusive(v___x_1567_)) as u8;
                    if v_isSharedCheck_1599_ == 0 {
                        v___x_1594_ = v___x_1567_;
                        v_isShared_1595_ = v_isSharedCheck_1599_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1592_);
                        crate::leanh::lean_dec(v___x_1567_);
                        v___x_1594_ = crate::leanh::lean_box(0);
                        v_isShared_1595_ = v_isSharedCheck_1599_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1572_ = (crate::leanh::lean_unbox(v_a_1568_) as u8);
                crate::leanh::lean_dec(v_a_1568_);
                if v___x_1572_ == 0 {
                    crate::leanh::lean_del_object(v___x_1570_);
                    v___x_1573_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2);
                    v___x_1574_ = l_Lean_MessageData_ofName(v_declName_1516_);
                    v___x_1575_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1573_);
                    crate::leanh::lean_ctor_set(v___x_1575_, 1, v___x_1574_);
                    v___x_1576_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4);
                    v___x_1577_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1577_, 0, v___x_1575_);
                    crate::leanh::lean_ctor_set(v___x_1577_, 1, v___x_1576_);
                    v___x_1578_ = l_Lean_indentExpr(v_inst_1517_);
                    v___x_1579_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1579_, 0, v___x_1577_);
                    crate::leanh::lean_ctor_set(v___x_1579_, 1, v___x_1578_);
                    v___x_1580_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6);
                    v___x_1581_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1579_);
                    crate::leanh::lean_ctor_set(v___x_1581_, 1, v___x_1580_);
                    v___x_1582_ = l_Lean_indentExpr(v_inst_x27_1518_);
                    v___x_1583_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1583_, 0, v___x_1581_);
                    crate::leanh::lean_ctor_set(v___x_1583_, 1, v___x_1582_);
                    v___x_1584_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8);
                    v___x_1585_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1585_, 0, v___x_1583_);
                    crate::leanh::lean_ctor_set(v___x_1585_, 1, v___x_1584_);
                    v___x_1586_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_1585_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
                    return v___x_1586_;
                } else {
                    crate::leanh::lean_dec_ref(v_inst_x27_1518_);
                    crate::leanh::lean_dec_ref(v_inst_1517_);
                    crate::leanh::lean_dec(v_declName_1516_);
                    v___x_1587_ = crate::leanh::lean_box(0);
                    if v_isShared_1571_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1587_);
                        v___x_1589_ = v___x_1570_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1590_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
                        v___x_1589_ = v_reuseFailAlloc_1590_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1589_;
            }
            5 => {
                if v_isShared_1595_ == 0 {
                    v___x_1597_ = v___x_1594_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
                    v___x_1597_ = v_reuseFailAlloc_1598_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(
    mut v_declName_1602_: *mut crate::leanh::LeanObject,
    mut v_inst_1603_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1610_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(
        v_declName_1602_,
        v_inst_1603_,
        v_inst_x27_1604_,
        v_a_1605_,
        v_a_1606_,
        v_a_1607_,
        v_a_1608_,
    );
    crate::leanh::lean_dec(v_a_1608_);
    crate::leanh::lean_dec_ref(v_a_1607_);
    crate::leanh::lean_dec(v_a_1606_);
    crate::leanh::lean_dec_ref(v_a_1605_);
    return v_res_1610_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(
    mut v_00_u03b1_1611_: *mut crate::leanh::LeanObject,
    mut v_msg_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
    return v___x_1618_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(
    mut v_00_u03b1_1619_: *mut crate::leanh::LeanObject,
    mut v_msg_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_1619_, v_msg_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
    crate::leanh::lean_dec(v___y_1624_);
    crate::leanh::lean_dec_ref(v___y_1623_);
    crate::leanh::lean_dec(v___y_1622_);
    crate::leanh::lean_dec_ref(v___y_1621_);
    return v_res_1626_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(
    mut v_inst_1627_: *mut crate::leanh::LeanObject,
    mut v_declName_1628_: *mut crate::leanh::LeanObject,
    mut v___x_1629_: *mut crate::leanh::LeanObject,
    mut v_type_1630_: *mut crate::leanh::LeanObject,
    mut v_inst_1631_: *mut crate::leanh::LeanObject,
    mut v_____r_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1633_ = crate::leanh::lean_ctor_get(v_inst_1627_, 0);
    crate::leanh::lean_inc(v_canonExpr_1633_);
    crate::leanh::lean_dec_ref(v_inst_1627_);
    v___x_1634_ = l_Lean_mkConst(v_declName_1628_, v___x_1629_);
    v___x_1635_ = l_Lean_mkAppB(v___x_1634_, v_type_1630_, v_inst_1631_);
    v___x_1636_ = crate::leanh::lean_apply_1(v_canonExpr_1633_, v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(
    mut v_inst_1637_: *mut crate::leanh::LeanObject,
    mut v_declName_1638_: *mut crate::leanh::LeanObject,
    mut v___x_1639_: *mut crate::leanh::LeanObject,
    mut v_type_1640_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1641_: *mut crate::leanh::LeanObject,
    mut v_inst_1642_: *mut crate::leanh::LeanObject,
    mut v_toBind_1643_: *mut crate::leanh::LeanObject,
    mut v_inst_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1644_);
    crate::leanh::lean_inc(v_declName_1638_);
    v___f_1645_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1645_, 0, v_inst_1637_);
    crate::leanh::lean_closure_set(v___f_1645_, 1, v_declName_1638_);
    crate::leanh::lean_closure_set(v___f_1645_, 2, v___x_1639_);
    crate::leanh::lean_closure_set(v___f_1645_, 3, v_type_1640_);
    crate::leanh::lean_closure_set(v___f_1645_, 4, v_inst_1644_);
    v___x_1646_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1646_, 0, v_declName_1638_);
    crate::leanh::lean_closure_set(v___x_1646_, 1, v_inst_1644_);
    crate::leanh::lean_closure_set(v___x_1646_, 2, v_expectedInst_1641_);
    v___x_1647_ = crate::leanh::lean_apply_2(v_inst_1642_, crate::leanh::lean_box(0), v___x_1646_);
    v___x_1648_ = crate::leanh::lean_apply_4(
        v_toBind_1643_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1647_,
        v___f_1645_,
    );
    return v___x_1648_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(
    mut v_inst_1649_: *mut crate::leanh::LeanObject,
    mut v_inst_1650_: *mut crate::leanh::LeanObject,
    mut v_inst_1651_: *mut crate::leanh::LeanObject,
    mut v_inst_1652_: *mut crate::leanh::LeanObject,
    mut v_type_1653_: *mut crate::leanh::LeanObject,
    mut v_u_1654_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1655_: *mut crate::leanh::LeanObject,
    mut v_declName_1656_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1658_ = crate::leanh::lean_ctor_get(v_inst_1651_, 1);
    crate::leanh::lean_inc_n(v_toBind_1658_, 2);
    v___x_1659_ = crate::leanh::lean_box(0);
    v___x_1660_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1660_, 0, v_u_1654_);
    crate::leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
    crate::leanh::lean_inc_ref(v_type_1653_);
    crate::leanh::lean_inc_ref(v___x_1660_);
    crate::leanh::lean_inc_ref(v_inst_1652_);
    v___f_1661_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1
            as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1661_, 0, v_inst_1652_);
    crate::leanh::lean_closure_set(v___f_1661_, 1, v_declName_1656_);
    crate::leanh::lean_closure_set(v___f_1661_, 2, v___x_1660_);
    crate::leanh::lean_closure_set(v___f_1661_, 3, v_type_1653_);
    crate::leanh::lean_closure_set(v___f_1661_, 4, v_expectedInst_1657_);
    crate::leanh::lean_closure_set(v___f_1661_, 5, v_inst_1649_);
    crate::leanh::lean_closure_set(v___f_1661_, 6, v_toBind_1658_);
    v___x_1662_ = l_Lean_mkConst(v_instDeclName_1655_, v___x_1660_);
    v___x_1663_ = l_Lean_Expr_app___override(v___x_1662_, v_type_1653_);
    v___x_1664_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1651_,
        v_inst_1650_,
        v_inst_1652_,
        v___x_1663_,
    );
    v___x_1665_ = crate::leanh::lean_apply_4(
        v_toBind_1658_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1664_,
        v___f_1661_,
    );
    return v___x_1665_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(
    mut v_m_1666_: *mut crate::leanh::LeanObject,
    mut v_inst_1667_: *mut crate::leanh::LeanObject,
    mut v_inst_1668_: *mut crate::leanh::LeanObject,
    mut v_inst_1669_: *mut crate::leanh::LeanObject,
    mut v_inst_1670_: *mut crate::leanh::LeanObject,
    mut v_type_1671_: *mut crate::leanh::LeanObject,
    mut v_u_1672_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1673_: *mut crate::leanh::LeanObject,
    mut v_declName_1674_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(
            v_inst_1667_,
            v_inst_1668_,
            v_inst_1669_,
            v_inst_1670_,
            v_type_1671_,
            v_u_1672_,
            v_instDeclName_1673_,
            v_declName_1674_,
            v_expectedInst_1675_,
        );
    return v___x_1676_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(
    mut v_inst_1677_: *mut crate::leanh::LeanObject,
    mut v_declName_1678_: *mut crate::leanh::LeanObject,
    mut v___x_1679_: *mut crate::leanh::LeanObject,
    mut v_type_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
    mut v_____r_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1683_ = crate::leanh::lean_ctor_get(v_inst_1677_, 0);
    crate::leanh::lean_inc(v_canonExpr_1683_);
    crate::leanh::lean_dec_ref(v_inst_1677_);
    v___x_1684_ = l_Lean_mkConst(v_declName_1678_, v___x_1679_);
    crate::leanh::lean_inc_ref_n(v_type_1680_, 2);
    v___x_1685_ = l_Lean_mkApp4(
        v___x_1684_,
        v_type_1680_,
        v_type_1680_,
        v_type_1680_,
        v_inst_1681_,
    );
    v___x_1686_ = crate::leanh::lean_apply_1(v_canonExpr_1683_, v___x_1685_);
    return v___x_1686_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(
    mut v_inst_1687_: *mut crate::leanh::LeanObject,
    mut v_declName_1688_: *mut crate::leanh::LeanObject,
    mut v___x_1689_: *mut crate::leanh::LeanObject,
    mut v_type_1690_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1691_: *mut crate::leanh::LeanObject,
    mut v_inst_1692_: *mut crate::leanh::LeanObject,
    mut v_toBind_1693_: *mut crate::leanh::LeanObject,
    mut v_inst_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1694_);
    crate::leanh::lean_inc(v_declName_1688_);
    v___f_1695_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___f_1695_, 0, v_inst_1687_);
    crate::leanh::lean_closure_set(v___f_1695_, 1, v_declName_1688_);
    crate::leanh::lean_closure_set(v___f_1695_, 2, v___x_1689_);
    crate::leanh::lean_closure_set(v___f_1695_, 3, v_type_1690_);
    crate::leanh::lean_closure_set(v___f_1695_, 4, v_inst_1694_);
    v___x_1696_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1696_, 0, v_declName_1688_);
    crate::leanh::lean_closure_set(v___x_1696_, 1, v_inst_1694_);
    crate::leanh::lean_closure_set(v___x_1696_, 2, v_expectedInst_1691_);
    v___x_1697_ = crate::leanh::lean_apply_2(v_inst_1692_, crate::leanh::lean_box(0), v___x_1696_);
    v___x_1698_ = crate::leanh::lean_apply_4(
        v_toBind_1693_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1697_,
        v___f_1695_,
    );
    return v___x_1698_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
    mut v_inst_1699_: *mut crate::leanh::LeanObject,
    mut v_inst_1700_: *mut crate::leanh::LeanObject,
    mut v_inst_1701_: *mut crate::leanh::LeanObject,
    mut v_inst_1702_: *mut crate::leanh::LeanObject,
    mut v_type_1703_: *mut crate::leanh::LeanObject,
    mut v_u_1704_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1705_: *mut crate::leanh::LeanObject,
    mut v_declName_1706_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1708_ = crate::leanh::lean_ctor_get(v_inst_1701_, 1);
    crate::leanh::lean_inc_n(v_toBind_1708_, 2);
    v___x_1709_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_n(v_u_1704_, 2);
    v___x_1710_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1710_, 0, v_u_1704_);
    crate::leanh::lean_ctor_set(v___x_1710_, 1, v___x_1709_);
    v___x_1711_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1711_, 0, v_u_1704_);
    crate::leanh::lean_ctor_set(v___x_1711_, 1, v___x_1710_);
    v___x_1712_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1712_, 0, v_u_1704_);
    crate::leanh::lean_ctor_set(v___x_1712_, 1, v___x_1711_);
    crate::leanh::lean_inc_ref_n(v_type_1703_, 3);
    crate::leanh::lean_inc_ref(v___x_1712_);
    crate::leanh::lean_inc_ref(v_inst_1702_);
    v___f_1713_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1 as *mut core::ffi::c_void, 8, 7);
    crate::leanh::lean_closure_set(v___f_1713_, 0, v_inst_1702_);
    crate::leanh::lean_closure_set(v___f_1713_, 1, v_declName_1706_);
    crate::leanh::lean_closure_set(v___f_1713_, 2, v___x_1712_);
    crate::leanh::lean_closure_set(v___f_1713_, 3, v_type_1703_);
    crate::leanh::lean_closure_set(v___f_1713_, 4, v_expectedInst_1707_);
    crate::leanh::lean_closure_set(v___f_1713_, 5, v_inst_1699_);
    crate::leanh::lean_closure_set(v___f_1713_, 6, v_toBind_1708_);
    v___x_1714_ = l_Lean_mkConst(v_instDeclName_1705_, v___x_1712_);
    v___x_1715_ = l_Lean_mkApp3(v___x_1714_, v_type_1703_, v_type_1703_, v_type_1703_);
    v___x_1716_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1701_,
        v_inst_1700_,
        v_inst_1702_,
        v___x_1715_,
    );
    v___x_1717_ = crate::leanh::lean_apply_4(
        v_toBind_1708_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1716_,
        v___f_1713_,
    );
    return v___x_1717_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(
    mut v_m_1718_: *mut crate::leanh::LeanObject,
    mut v_inst_1719_: *mut crate::leanh::LeanObject,
    mut v_inst_1720_: *mut crate::leanh::LeanObject,
    mut v_inst_1721_: *mut crate::leanh::LeanObject,
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
    mut v_type_1723_: *mut crate::leanh::LeanObject,
    mut v_u_1724_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1725_: *mut crate::leanh::LeanObject,
    mut v_declName_1726_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
            v_inst_1719_,
            v_inst_1720_,
            v_inst_1721_,
            v_inst_1722_,
            v_type_1723_,
            v_u_1724_,
            v_instDeclName_1725_,
            v_declName_1726_,
            v_expectedInst_1727_,
        );
    return v___x_1728_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(
    mut v_inst_1729_: *mut crate::leanh::LeanObject,
    mut v___x_1730_: *mut crate::leanh::LeanObject,
    mut v___x_1731_: *mut crate::leanh::LeanObject,
    mut v_type_1732_: *mut crate::leanh::LeanObject,
    mut v___x_1733_: *mut crate::leanh::LeanObject,
    mut v_inst_1734_: *mut crate::leanh::LeanObject,
    mut v_____r_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1736_ = crate::leanh::lean_ctor_get(v_inst_1729_, 0);
    crate::leanh::lean_inc(v_canonExpr_1736_);
    crate::leanh::lean_dec_ref(v_inst_1729_);
    v___x_1737_ = l_Lean_mkConst(v___x_1730_, v___x_1731_);
    crate::leanh::lean_inc_ref(v_type_1732_);
    v___x_1738_ = l_Lean_mkApp4(
        v___x_1737_,
        v_type_1732_,
        v___x_1733_,
        v_type_1732_,
        v_inst_1734_,
    );
    v___x_1739_ = crate::leanh::lean_apply_1(v_canonExpr_1736_, v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(
    mut v___x_1750_: *mut crate::leanh::LeanObject,
    mut v_type_1751_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1752_: *mut crate::leanh::LeanObject,
    mut v___x_1753_: *mut crate::leanh::LeanObject,
    mut v_inst_1754_: *mut crate::leanh::LeanObject,
    mut v___x_1755_: *mut crate::leanh::LeanObject,
    mut v___x_1756_: *mut crate::leanh::LeanObject,
    mut v_inst_1757_: *mut crate::leanh::LeanObject,
    mut v_toBind_1758_: *mut crate::leanh::LeanObject,
    mut v_inst_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4;
    v___x_1761_ = l_Lean_mkConst(v___x_1760_, v___x_1750_);
    crate::leanh::lean_inc_ref(v_type_1751_);
    v_inst_x27_1762_ = l_Lean_mkAppB(v___x_1761_, v_type_1751_, v_semiringInst_1752_);
    v___x_1763_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5;
    v___x_1764_ = l_Lean_Name_mkStr2(v___x_1753_, v___x_1763_);
    crate::leanh::lean_inc_ref(v_inst_1759_);
    crate::leanh::lean_inc(v___x_1764_);
    v___f_1765_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0
            as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1765_, 0, v_inst_1754_);
    crate::leanh::lean_closure_set(v___f_1765_, 1, v___x_1764_);
    crate::leanh::lean_closure_set(v___f_1765_, 2, v___x_1755_);
    crate::leanh::lean_closure_set(v___f_1765_, 3, v_type_1751_);
    crate::leanh::lean_closure_set(v___f_1765_, 4, v___x_1756_);
    crate::leanh::lean_closure_set(v___f_1765_, 5, v_inst_1759_);
    v___x_1766_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1766_, 0, v___x_1764_);
    crate::leanh::lean_closure_set(v___x_1766_, 1, v_inst_1759_);
    crate::leanh::lean_closure_set(v___x_1766_, 2, v_inst_x27_1762_);
    v___x_1767_ = crate::leanh::lean_apply_2(v_inst_1757_, crate::leanh::lean_box(0), v___x_1766_);
    v___x_1768_ = crate::leanh::lean_apply_4(
        v_toBind_1758_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1767_,
        v___f_1765_,
    );
    return v___x_1768_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1772_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1773_ = l_Lean_Level_ofNat(v___x_1772_);
    return v___x_1773_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(
    mut v_inst_1774_: *mut crate::leanh::LeanObject,
    mut v_inst_1775_: *mut crate::leanh::LeanObject,
    mut v_inst_1776_: *mut crate::leanh::LeanObject,
    mut v_inst_1777_: *mut crate::leanh::LeanObject,
    mut v_u_1778_: *mut crate::leanh::LeanObject,
    mut v_type_1779_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1781_ = crate::leanh::lean_ctor_get(v_inst_1776_, 1);
    crate::leanh::lean_inc_n(v_toBind_1781_, 2);
    v___x_1782_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0;
    v___x_1783_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1;
    v___x_1784_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
    v___x_1785_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_u_1778_);
    v___x_1786_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1786_, 0, v_u_1778_);
    crate::leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
    crate::leanh::lean_inc_ref(v___x_1786_);
    v___x_1787_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1784_);
    crate::leanh::lean_ctor_set(v___x_1787_, 1, v___x_1786_);
    v___x_1788_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1788_, 0, v_u_1778_);
    crate::leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
    crate::leanh::lean_inc_ref(v___x_1788_);
    v___x_1789_ = l_Lean_mkConst(v___x_1783_, v___x_1788_);
    v___x_1790_ = l_Lean_Nat_mkType;
    crate::leanh::lean_inc_ref(v_inst_1777_);
    crate::leanh::lean_inc_ref_n(v_type_1779_, 2);
    v___f_1791_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1
            as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1791_, 0, v___x_1786_);
    crate::leanh::lean_closure_set(v___f_1791_, 1, v_type_1779_);
    crate::leanh::lean_closure_set(v___f_1791_, 2, v_semiringInst_1780_);
    crate::leanh::lean_closure_set(v___f_1791_, 3, v___x_1782_);
    crate::leanh::lean_closure_set(v___f_1791_, 4, v_inst_1777_);
    crate::leanh::lean_closure_set(v___f_1791_, 5, v___x_1788_);
    crate::leanh::lean_closure_set(v___f_1791_, 6, v___x_1790_);
    crate::leanh::lean_closure_set(v___f_1791_, 7, v_inst_1774_);
    crate::leanh::lean_closure_set(v___f_1791_, 8, v_toBind_1781_);
    v___x_1792_ = l_Lean_mkApp3(v___x_1789_, v_type_1779_, v___x_1790_, v_type_1779_);
    v___x_1793_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1776_,
        v_inst_1775_,
        v_inst_1777_,
        v___x_1792_,
    );
    v___x_1794_ = crate::leanh::lean_apply_4(
        v_toBind_1781_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1793_,
        v___f_1791_,
    );
    return v___x_1794_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(
    mut v_m_1795_: *mut crate::leanh::LeanObject,
    mut v_inst_1796_: *mut crate::leanh::LeanObject,
    mut v_inst_1797_: *mut crate::leanh::LeanObject,
    mut v_inst_1798_: *mut crate::leanh::LeanObject,
    mut v_inst_1799_: *mut crate::leanh::LeanObject,
    mut v_u_1800_: *mut crate::leanh::LeanObject,
    mut v_type_1801_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(
        v_inst_1796_,
        v_inst_1797_,
        v_inst_1798_,
        v_inst_1799_,
        v_u_1800_,
        v_type_1801_,
        v_semiringInst_1802_,
    );
    return v___x_1803_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(
    mut v___x_1804_: *mut crate::leanh::LeanObject,
    mut v___x_1805_: *mut crate::leanh::LeanObject,
    mut v___x_1806_: *mut crate::leanh::LeanObject,
    mut v_type_1807_: *mut crate::leanh::LeanObject,
    mut v_canonExpr_1808_: *mut crate::leanh::LeanObject,
    mut v_inst_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = l_Lean_Name_mkStr2(v___x_1804_, v___x_1805_);
    v___x_1811_ = l_Lean_mkConst(v___x_1810_, v___x_1806_);
    v___x_1812_ = l_Lean_mkAppB(v___x_1811_, v_type_1807_, v_inst_1809_);
    v___x_1813_ = crate::leanh::lean_apply_1(v_canonExpr_1808_, v___x_1812_);
    return v___x_1813_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(
    mut v___f_1814_: *mut crate::leanh::LeanObject,
    mut v_inst_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = crate::leanh::lean_apply_1(v___f_1814_, v_inst_1815_);
    return v___x_1816_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(
    mut v_toPure_1817_: *mut crate::leanh::LeanObject,
    mut v_val_1818_: *mut crate::leanh::LeanObject,
    mut v_toBind_1819_: *mut crate::leanh::LeanObject,
    mut v___f_1820_: *mut crate::leanh::LeanObject,
    mut v_____r_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ =
        crate::leanh::lean_apply_2(v_toPure_1817_, crate::leanh::lean_box(0), v_val_1818_);
    v___x_1823_ = crate::leanh::lean_apply_4(
        v_toBind_1819_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1822_,
        v___f_1820_,
    );
    return v___x_1823_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(
    mut v_toPure_1824_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_1825_: *mut crate::leanh::LeanObject,
    mut v_toBind_1826_: *mut crate::leanh::LeanObject,
    mut v___f_1827_: *mut crate::leanh::LeanObject,
    mut v___f_1828_: *mut crate::leanh::LeanObject,
    mut v___x_1829_: *mut crate::leanh::LeanObject,
    mut v___x_1830_: *mut crate::leanh::LeanObject,
    mut v_inst_1831_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1832_) == 0 {
        let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_1831_);
        crate::leanh::lean_dec_ref(v___x_1830_);
        crate::leanh::lean_dec_ref(v___x_1829_);
        crate::leanh::lean_dec(v___f_1828_);
        v___x_1833_ =
            crate::leanh::lean_apply_2(v_toPure_1824_, crate::leanh::lean_box(0), v_inst_x27_1825_);
        v___x_1834_ = crate::leanh::lean_apply_4(
            v_toBind_1826_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1833_,
            v___f_1827_,
        );
        return v___x_1834_;
    } else {
        let mut v_val_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1827_);
        v_val_1835_ = crate::leanh::lean_ctor_get(v_____do__lift_1832_, 0);
        crate::leanh::lean_inc_n(v_val_1835_, 2);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1832_, 1);
        crate::leanh::lean_inc(v_toBind_1826_);
        v___f_1836_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_1836_, 0, v_toPure_1824_);
        crate::leanh::lean_closure_set(v___f_1836_, 1, v_val_1835_);
        crate::leanh::lean_closure_set(v___f_1836_, 2, v_toBind_1826_);
        crate::leanh::lean_closure_set(v___f_1836_, 3, v___f_1828_);
        v___x_1837_ = l_Lean_Name_mkStr2(v___x_1829_, v___x_1830_);
        v___x_1838_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
                as *mut core::ffi::c_void,
            8,
            3,
        );
        crate::leanh::lean_closure_set(v___x_1838_, 0, v___x_1837_);
        crate::leanh::lean_closure_set(v___x_1838_, 1, v_val_1835_);
        crate::leanh::lean_closure_set(v___x_1838_, 2, v_inst_x27_1825_);
        v___x_1839_ =
            crate::leanh::lean_apply_2(v_inst_1831_, crate::leanh::lean_box(0), v___x_1838_);
        v___x_1840_ = crate::leanh::lean_apply_4(
            v_toBind_1826_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1839_,
            v___f_1836_,
        );
        return v___x_1840_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(
    mut v_inst_1850_: *mut crate::leanh::LeanObject,
    mut v_inst_1851_: *mut crate::leanh::LeanObject,
    mut v_inst_1852_: *mut crate::leanh::LeanObject,
    mut v_u_1853_: *mut crate::leanh::LeanObject,
    mut v_type_1854_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v_toPure_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instType_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1856_ = crate::leanh::lean_ctor_get(v_inst_1851_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1856_);
                v_toBind_1857_ = crate::leanh::lean_ctor_get(v_inst_1851_, 1);
                crate::leanh::lean_inc(v_toBind_1857_);
                crate::leanh::lean_dec_ref(v_inst_1851_);
                v_canonExpr_1858_ = crate::leanh::lean_ctor_get(v_inst_1852_, 0);
                v_synthInstance_x3f_1859_ = crate::leanh::lean_ctor_get(v_inst_1852_, 1);
                v_isSharedCheck_1881_ = (!crate::leanh::lean_is_exclusive(v_inst_1852_)) as u8;
                if v_isSharedCheck_1881_ == 0 {
                    v___x_1861_ = v_inst_1852_;
                    v_isShared_1862_ = v_isSharedCheck_1881_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_synthInstance_x3f_1859_);
                    crate::leanh::lean_inc(v_canonExpr_1858_);
                    crate::leanh::lean_dec(v_inst_1852_);
                    v___x_1861_ = crate::leanh::lean_box(0);
                    v_isShared_1862_ = v_isSharedCheck_1881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1863_ = crate::leanh::lean_ctor_get(v_toApplicative_1856_, 1);
                crate::leanh::lean_inc(v_toPure_1863_);
                crate::leanh::lean_dec_ref(v_toApplicative_1856_);
                v___x_1864_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0;
                v___x_1865_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1;
                v___x_1866_ = crate::leanh::lean_box(0);
                if v_isShared_1862_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1861_, 1);
                    crate::leanh::lean_ctor_set(v___x_1861_, 1, v___x_1866_);
                    crate::leanh::lean_ctor_set(v___x_1861_, 0, v_u_1853_);
                    v___x_1868_ = v___x_1861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_u_1853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1866_);
                    v___x_1868_ = v_reuseFailAlloc_1880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___x_1868_, 2);
                v___x_1869_ = l_Lean_mkConst(v___x_1865_, v___x_1868_);
                crate::leanh::lean_inc_ref_n(v_type_1854_, 2);
                v_inst_x27_1870_ = l_Lean_mkAppB(v___x_1869_, v_type_1854_, v_semiringInst_1855_);
                v___x_1871_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2;
                v___f_1872_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                crate::leanh::lean_closure_set(v___f_1872_, 0, v___x_1871_);
                crate::leanh::lean_closure_set(v___f_1872_, 1, v___x_1864_);
                crate::leanh::lean_closure_set(v___f_1872_, 2, v___x_1868_);
                crate::leanh::lean_closure_set(v___f_1872_, 3, v_type_1854_);
                crate::leanh::lean_closure_set(v___f_1872_, 4, v_canonExpr_1858_);
                v___f_1873_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_1873_, 0, v___f_1872_);
                v___x_1874_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3;
                v___x_1875_ = l_Lean_mkConst(v___x_1874_, v___x_1868_);
                v_instType_1876_ = l_Lean_Expr_app___override(v___x_1875_, v_type_1854_);
                v___x_1877_ =
                    crate::leanh::lean_apply_1(v_synthInstance_x3f_1859_, v_instType_1876_);
                crate::leanh::lean_inc_ref(v___f_1873_);
                crate::leanh::lean_inc(v_toBind_1857_);
                v___f_1878_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2 as *mut core::ffi::c_void, 9, 8);
                crate::leanh::lean_closure_set(v___f_1878_, 0, v_toPure_1863_);
                crate::leanh::lean_closure_set(v___f_1878_, 1, v_inst_x27_1870_);
                crate::leanh::lean_closure_set(v___f_1878_, 2, v_toBind_1857_);
                crate::leanh::lean_closure_set(v___f_1878_, 3, v___f_1873_);
                crate::leanh::lean_closure_set(v___f_1878_, 4, v___f_1873_);
                crate::leanh::lean_closure_set(v___f_1878_, 5, v___x_1871_);
                crate::leanh::lean_closure_set(v___f_1878_, 6, v___x_1864_);
                crate::leanh::lean_closure_set(v___f_1878_, 7, v_inst_1850_);
                v___x_1879_ = crate::leanh::lean_apply_4(
                    v_toBind_1857_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1877_,
                    v___f_1878_,
                );
                return v___x_1879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(
    mut v_m_1882_: *mut crate::leanh::LeanObject,
    mut v_inst_1883_: *mut crate::leanh::LeanObject,
    mut v_inst_1884_: *mut crate::leanh::LeanObject,
    mut v_inst_1885_: *mut crate::leanh::LeanObject,
    mut v_u_1886_: *mut crate::leanh::LeanObject,
    mut v_type_1887_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(
            v_inst_1883_,
            v_inst_1884_,
            v_inst_1885_,
            v_u_1886_,
            v_type_1887_,
            v_semiringInst_1888_,
        );
    return v___x_1889_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(
    mut v_addFn_1890_: *mut crate::leanh::LeanObject,
    mut v_s_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut v_unused_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1892_ = crate::leanh::lean_ctor_get(v_s_1891_, 0);
                v_type_1893_ = crate::leanh::lean_ctor_get(v_s_1891_, 1);
                v_u_1894_ = crate::leanh::lean_ctor_get(v_s_1891_, 2);
                v_ringInst_1895_ = crate::leanh::lean_ctor_get(v_s_1891_, 3);
                v_semiringInst_1896_ = crate::leanh::lean_ctor_get(v_s_1891_, 4);
                v_charInst_x3f_1897_ = crate::leanh::lean_ctor_get(v_s_1891_, 5);
                v_mulFn_x3f_1898_ = crate::leanh::lean_ctor_get(v_s_1891_, 7);
                v_subFn_x3f_1899_ = crate::leanh::lean_ctor_get(v_s_1891_, 8);
                v_negFn_x3f_1900_ = crate::leanh::lean_ctor_get(v_s_1891_, 9);
                v_powFn_x3f_1901_ = crate::leanh::lean_ctor_get(v_s_1891_, 10);
                v_intCastFn_x3f_1902_ = crate::leanh::lean_ctor_get(v_s_1891_, 11);
                v_natCastFn_x3f_1903_ = crate::leanh::lean_ctor_get(v_s_1891_, 12);
                v_one_x3f_1904_ = crate::leanh::lean_ctor_get(v_s_1891_, 13);
                v_isSharedCheck_1912_ = (!crate::leanh::lean_is_exclusive(v_s_1891_)) as u8;
                if v_isSharedCheck_1912_ == 0 {
                    v_unused_1913_ = crate::leanh::lean_ctor_get(v_s_1891_, 6);
                    crate::leanh::lean_dec(v_unused_1913_);
                    v___x_1906_ = v_s_1891_;
                    v_isShared_1907_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_one_x3f_1904_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_1903_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_1902_);
                    crate::leanh::lean_inc(v_powFn_x3f_1901_);
                    crate::leanh::lean_inc(v_negFn_x3f_1900_);
                    crate::leanh::lean_inc(v_subFn_x3f_1899_);
                    crate::leanh::lean_inc(v_mulFn_x3f_1898_);
                    crate::leanh::lean_inc(v_charInst_x3f_1897_);
                    crate::leanh::lean_inc(v_semiringInst_1896_);
                    crate::leanh::lean_inc(v_ringInst_1895_);
                    crate::leanh::lean_inc(v_u_1894_);
                    crate::leanh::lean_inc(v_type_1893_);
                    crate::leanh::lean_inc(v_id_1892_);
                    crate::leanh::lean_dec(v_s_1891_);
                    v___x_1906_ = crate::leanh::lean_box(0);
                    v_isShared_1907_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1908_, 0, v_addFn_1890_);
                if v_isShared_1907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1906_, 6, v___x_1908_);
                    v___x_1910_ = v___x_1906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_id_1892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_type_1893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_u_1894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_ringInst_1895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_semiringInst_1896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 5, v_charInst_x3f_1897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 6, v___x_1908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 7, v_mulFn_x3f_1898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 8, v_subFn_x3f_1899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 9, v_negFn_x3f_1900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 10, v_powFn_x3f_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 11, v_intCastFn_x3f_1902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 12, v_natCastFn_x3f_1903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 13, v_one_x3f_1904_);
                    v___x_1910_ = v_reuseFailAlloc_1911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(
    mut v_toPure_1914_: *mut crate::leanh::LeanObject,
    mut v_addFn_1915_: *mut crate::leanh::LeanObject,
    mut v_____r_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ =
        crate::leanh::lean_apply_2(v_toPure_1914_, crate::leanh::lean_box(0), v_addFn_1915_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(
    mut v_toPure_1918_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_1919_: *mut crate::leanh::LeanObject,
    mut v_toBind_1920_: *mut crate::leanh::LeanObject,
    mut v_addFn_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_addFn_1921_);
    v___f_1922_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1922_, 0, v_addFn_1921_);
    v___f_1923_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1923_, 0, v_toPure_1918_);
    crate::leanh::lean_closure_set(v___f_1923_, 1, v_addFn_1921_);
    v___x_1924_ = crate::leanh::lean_apply_1(v_modifyRing_1919_, v___f_1922_);
    v___x_1925_ = crate::leanh::lean_apply_4(
        v_toBind_1920_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1924_,
        v___f_1923_,
    );
    return v___x_1925_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(
    mut v_toPure_1942_: *mut crate::leanh::LeanObject,
    mut v_inst_1943_: *mut crate::leanh::LeanObject,
    mut v_inst_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_toBind_1947_: *mut crate::leanh::LeanObject,
    mut v___f_1948_: *mut crate::leanh::LeanObject,
    mut v_ring_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_addFn_x3f_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_addFn_x3f_1950_ = crate::leanh::lean_ctor_get(v_ring_1949_, 6);
    if crate::leanh::lean_obj_tag(v_addFn_x3f_1950_) == 1 {
        let mut v_val_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_addFn_x3f_1950_);
        crate::leanh::lean_dec_ref(v_ring_1949_);
        crate::leanh::lean_dec(v___f_1948_);
        crate::leanh::lean_dec(v_toBind_1947_);
        crate::leanh::lean_dec_ref(v_inst_1946_);
        crate::leanh::lean_dec_ref(v_inst_1945_);
        crate::leanh::lean_dec_ref(v_inst_1944_);
        crate::leanh::lean_dec(v_inst_1943_);
        v_val_1951_ = crate::leanh::lean_ctor_get(v_addFn_x3f_1950_, 0);
        crate::leanh::lean_inc(v_val_1951_);
        crate::leanh::lean_dec_ref_known(v_addFn_x3f_1950_, 1);
        v___x_1952_ =
            crate::leanh::lean_apply_2(v_toPure_1942_, crate::leanh::lean_box(0), v_val_1951_);
        return v___x_1952_;
    } else {
        let mut v_type_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1942_);
        v_type_1953_ = crate::leanh::lean_ctor_get(v_ring_1949_, 1);
        crate::leanh::lean_inc_ref_n(v_type_1953_, 3);
        v_u_1954_ = crate::leanh::lean_ctor_get(v_ring_1949_, 2);
        crate::leanh::lean_inc_n(v_u_1954_, 2);
        v_semiringInst_1955_ = crate::leanh::lean_ctor_get(v_ring_1949_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_1955_);
        crate::leanh::lean_dec_ref(v_ring_1949_);
        v___x_1956_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1;
        v___x_1957_ = crate::leanh::lean_box(0);
        v___x_1958_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1958_, 0, v_u_1954_);
        crate::leanh::lean_ctor_set(v___x_1958_, 1, v___x_1957_);
        crate::leanh::lean_inc_ref(v___x_1958_);
        v___x_1959_ = l_Lean_mkConst(v___x_1956_, v___x_1958_);
        v___x_1960_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3;
        v___x_1961_ = l_Lean_mkConst(v___x_1960_, v___x_1958_);
        v___x_1962_ = l_Lean_mkAppB(v___x_1961_, v_type_1953_, v_semiringInst_1955_);
        v_expectedInst_1963_ = l_Lean_mkAppB(v___x_1959_, v_type_1953_, v___x_1962_);
        v___x_1964_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5;
        v___x_1965_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7;
        v___x_1966_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
                v_inst_1943_,
                v_inst_1944_,
                v_inst_1945_,
                v_inst_1946_,
                v_type_1953_,
                v_u_1954_,
                v___x_1964_,
                v___x_1965_,
                v_expectedInst_1963_,
            );
        v___x_1967_ = crate::leanh::lean_apply_4(
            v_toBind_1947_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1966_,
            v___f_1948_,
        );
        return v___x_1967_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg(
    mut v_inst_1968_: *mut crate::leanh::LeanObject,
    mut v_inst_1969_: *mut crate::leanh::LeanObject,
    mut v_inst_1970_: *mut crate::leanh::LeanObject,
    mut v_inst_1971_: *mut crate::leanh::LeanObject,
    mut v_inst_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1973_ = crate::leanh::lean_ctor_get(v_inst_1970_, 0);
    v_toBind_1974_ = crate::leanh::lean_ctor_get(v_inst_1970_, 1);
    crate::leanh::lean_inc_n(v_toBind_1974_, 3);
    v_getRing_1975_ = crate::leanh::lean_ctor_get(v_inst_1972_, 0);
    crate::leanh::lean_inc(v_getRing_1975_);
    v_modifyRing_1976_ = crate::leanh::lean_ctor_get(v_inst_1972_, 1);
    crate::leanh::lean_inc(v_modifyRing_1976_);
    crate::leanh::lean_dec_ref(v_inst_1972_);
    v_toPure_1977_ = crate::leanh::lean_ctor_get(v_toApplicative_1973_, 1);
    crate::leanh::lean_inc_n(v_toPure_1977_, 2);
    v___f_1978_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1978_, 0, v_toPure_1977_);
    crate::leanh::lean_closure_set(v___f_1978_, 1, v_modifyRing_1976_);
    crate::leanh::lean_closure_set(v___f_1978_, 2, v_toBind_1974_);
    v___f_1979_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1979_, 0, v_toPure_1977_);
    crate::leanh::lean_closure_set(v___f_1979_, 1, v_inst_1968_);
    crate::leanh::lean_closure_set(v___f_1979_, 2, v_inst_1969_);
    crate::leanh::lean_closure_set(v___f_1979_, 3, v_inst_1970_);
    crate::leanh::lean_closure_set(v___f_1979_, 4, v_inst_1971_);
    crate::leanh::lean_closure_set(v___f_1979_, 5, v_toBind_1974_);
    crate::leanh::lean_closure_set(v___f_1979_, 6, v___f_1978_);
    v___x_1980_ = crate::leanh::lean_apply_4(
        v_toBind_1974_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_1975_,
        v___f_1979_,
    );
    return v___x_1980_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn(
    mut v_m_1981_: *mut crate::leanh::LeanObject,
    mut v_inst_1982_: *mut crate::leanh::LeanObject,
    mut v_inst_1983_: *mut crate::leanh::LeanObject,
    mut v_inst_1984_: *mut crate::leanh::LeanObject,
    mut v_inst_1985_: *mut crate::leanh::LeanObject,
    mut v_inst_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1987_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(
        v_inst_1982_,
        v_inst_1983_,
        v_inst_1984_,
        v_inst_1985_,
        v_inst_1986_,
    );
    return v___x_1987_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(
    mut v_mulFn_1988_: *mut crate::leanh::LeanObject,
    mut v_s_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_unused_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1990_ = crate::leanh::lean_ctor_get(v_s_1989_, 0);
                v_type_1991_ = crate::leanh::lean_ctor_get(v_s_1989_, 1);
                v_u_1992_ = crate::leanh::lean_ctor_get(v_s_1989_, 2);
                v_ringInst_1993_ = crate::leanh::lean_ctor_get(v_s_1989_, 3);
                v_semiringInst_1994_ = crate::leanh::lean_ctor_get(v_s_1989_, 4);
                v_charInst_x3f_1995_ = crate::leanh::lean_ctor_get(v_s_1989_, 5);
                v_addFn_x3f_1996_ = crate::leanh::lean_ctor_get(v_s_1989_, 6);
                v_subFn_x3f_1997_ = crate::leanh::lean_ctor_get(v_s_1989_, 8);
                v_negFn_x3f_1998_ = crate::leanh::lean_ctor_get(v_s_1989_, 9);
                v_powFn_x3f_1999_ = crate::leanh::lean_ctor_get(v_s_1989_, 10);
                v_intCastFn_x3f_2000_ = crate::leanh::lean_ctor_get(v_s_1989_, 11);
                v_natCastFn_x3f_2001_ = crate::leanh::lean_ctor_get(v_s_1989_, 12);
                v_one_x3f_2002_ = crate::leanh::lean_ctor_get(v_s_1989_, 13);
                v_isSharedCheck_2010_ = (!crate::leanh::lean_is_exclusive(v_s_1989_)) as u8;
                if v_isSharedCheck_2010_ == 0 {
                    v_unused_2011_ = crate::leanh::lean_ctor_get(v_s_1989_, 7);
                    crate::leanh::lean_dec(v_unused_2011_);
                    v___x_2004_ = v_s_1989_;
                    v_isShared_2005_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_one_x3f_2002_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2001_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2000_);
                    crate::leanh::lean_inc(v_powFn_x3f_1999_);
                    crate::leanh::lean_inc(v_negFn_x3f_1998_);
                    crate::leanh::lean_inc(v_subFn_x3f_1997_);
                    crate::leanh::lean_inc(v_addFn_x3f_1996_);
                    crate::leanh::lean_inc(v_charInst_x3f_1995_);
                    crate::leanh::lean_inc(v_semiringInst_1994_);
                    crate::leanh::lean_inc(v_ringInst_1993_);
                    crate::leanh::lean_inc(v_u_1992_);
                    crate::leanh::lean_inc(v_type_1991_);
                    crate::leanh::lean_inc(v_id_1990_);
                    crate::leanh::lean_dec(v_s_1989_);
                    v___x_2004_ = crate::leanh::lean_box(0);
                    v_isShared_2005_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2006_, 0, v_mulFn_1988_);
                if v_isShared_2005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2004_, 7, v___x_2006_);
                    v___x_2008_ = v___x_2004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_id_1990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_type_1991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_u_1992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_ringInst_1993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_semiringInst_1994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 5, v_charInst_x3f_1995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 6, v_addFn_x3f_1996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 7, v___x_2006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 8, v_subFn_x3f_1997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 9, v_negFn_x3f_1998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 10, v_powFn_x3f_1999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 11, v_intCastFn_x3f_2000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 12, v_natCastFn_x3f_2001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 13, v_one_x3f_2002_);
                    v___x_2008_ = v_reuseFailAlloc_2009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(
    mut v_toPure_2012_: *mut crate::leanh::LeanObject,
    mut v_mulFn_2013_: *mut crate::leanh::LeanObject,
    mut v_____r_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ =
        crate::leanh::lean_apply_2(v_toPure_2012_, crate::leanh::lean_box(0), v_mulFn_2013_);
    return v___x_2015_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(
    mut v_toPure_2016_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2017_: *mut crate::leanh::LeanObject,
    mut v_toBind_2018_: *mut crate::leanh::LeanObject,
    mut v_mulFn_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_mulFn_2019_);
    v___f_2020_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2020_, 0, v_mulFn_2019_);
    v___f_2021_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2021_, 0, v_toPure_2016_);
    crate::leanh::lean_closure_set(v___f_2021_, 1, v_mulFn_2019_);
    v___x_2022_ = crate::leanh::lean_apply_1(v_modifyRing_2017_, v___f_2020_);
    v___x_2023_ = crate::leanh::lean_apply_4(
        v_toBind_2018_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2022_,
        v___f_2021_,
    );
    return v___x_2023_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(
    mut v_toPure_2040_: *mut crate::leanh::LeanObject,
    mut v_inst_2041_: *mut crate::leanh::LeanObject,
    mut v_inst_2042_: *mut crate::leanh::LeanObject,
    mut v_inst_2043_: *mut crate::leanh::LeanObject,
    mut v_inst_2044_: *mut crate::leanh::LeanObject,
    mut v_toBind_2045_: *mut crate::leanh::LeanObject,
    mut v___f_2046_: *mut crate::leanh::LeanObject,
    mut v_ring_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mulFn_x3f_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_2048_ = crate::leanh::lean_ctor_get(v_ring_2047_, 7);
    if crate::leanh::lean_obj_tag(v_mulFn_x3f_2048_) == 1 {
        let mut v_val_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_mulFn_x3f_2048_);
        crate::leanh::lean_dec_ref(v_ring_2047_);
        crate::leanh::lean_dec(v___f_2046_);
        crate::leanh::lean_dec(v_toBind_2045_);
        crate::leanh::lean_dec_ref(v_inst_2044_);
        crate::leanh::lean_dec_ref(v_inst_2043_);
        crate::leanh::lean_dec_ref(v_inst_2042_);
        crate::leanh::lean_dec(v_inst_2041_);
        v_val_2049_ = crate::leanh::lean_ctor_get(v_mulFn_x3f_2048_, 0);
        crate::leanh::lean_inc(v_val_2049_);
        crate::leanh::lean_dec_ref_known(v_mulFn_x3f_2048_, 1);
        v___x_2050_ =
            crate::leanh::lean_apply_2(v_toPure_2040_, crate::leanh::lean_box(0), v_val_2049_);
        return v___x_2050_;
    } else {
        let mut v_type_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2040_);
        v_type_2051_ = crate::leanh::lean_ctor_get(v_ring_2047_, 1);
        crate::leanh::lean_inc_ref_n(v_type_2051_, 3);
        v_u_2052_ = crate::leanh::lean_ctor_get(v_ring_2047_, 2);
        crate::leanh::lean_inc_n(v_u_2052_, 2);
        v_semiringInst_2053_ = crate::leanh::lean_ctor_get(v_ring_2047_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_2053_);
        crate::leanh::lean_dec_ref(v_ring_2047_);
        v___x_2054_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1;
        v___x_2055_ = crate::leanh::lean_box(0);
        v___x_2056_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2056_, 0, v_u_2052_);
        crate::leanh::lean_ctor_set(v___x_2056_, 1, v___x_2055_);
        crate::leanh::lean_inc_ref(v___x_2056_);
        v___x_2057_ = l_Lean_mkConst(v___x_2054_, v___x_2056_);
        v___x_2058_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3;
        v___x_2059_ = l_Lean_mkConst(v___x_2058_, v___x_2056_);
        v___x_2060_ = l_Lean_mkAppB(v___x_2059_, v_type_2051_, v_semiringInst_2053_);
        v_expectedInst_2061_ = l_Lean_mkAppB(v___x_2057_, v_type_2051_, v___x_2060_);
        v___x_2062_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5;
        v___x_2063_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7;
        v___x_2064_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
                v_inst_2041_,
                v_inst_2042_,
                v_inst_2043_,
                v_inst_2044_,
                v_type_2051_,
                v_u_2052_,
                v___x_2062_,
                v___x_2063_,
                v_expectedInst_2061_,
            );
        v___x_2065_ = crate::leanh::lean_apply_4(
            v_toBind_2045_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2064_,
            v___f_2046_,
        );
        return v___x_2065_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg(
    mut v_inst_2066_: *mut crate::leanh::LeanObject,
    mut v_inst_2067_: *mut crate::leanh::LeanObject,
    mut v_inst_2068_: *mut crate::leanh::LeanObject,
    mut v_inst_2069_: *mut crate::leanh::LeanObject,
    mut v_inst_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2071_ = crate::leanh::lean_ctor_get(v_inst_2068_, 0);
    v_toBind_2072_ = crate::leanh::lean_ctor_get(v_inst_2068_, 1);
    crate::leanh::lean_inc_n(v_toBind_2072_, 3);
    v_getRing_2073_ = crate::leanh::lean_ctor_get(v_inst_2070_, 0);
    crate::leanh::lean_inc(v_getRing_2073_);
    v_modifyRing_2074_ = crate::leanh::lean_ctor_get(v_inst_2070_, 1);
    crate::leanh::lean_inc(v_modifyRing_2074_);
    crate::leanh::lean_dec_ref(v_inst_2070_);
    v_toPure_2075_ = crate::leanh::lean_ctor_get(v_toApplicative_2071_, 1);
    crate::leanh::lean_inc_n(v_toPure_2075_, 2);
    v___f_2076_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2076_, 0, v_toPure_2075_);
    crate::leanh::lean_closure_set(v___f_2076_, 1, v_modifyRing_2074_);
    crate::leanh::lean_closure_set(v___f_2076_, 2, v_toBind_2072_);
    v___f_2077_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2077_, 0, v_toPure_2075_);
    crate::leanh::lean_closure_set(v___f_2077_, 1, v_inst_2066_);
    crate::leanh::lean_closure_set(v___f_2077_, 2, v_inst_2067_);
    crate::leanh::lean_closure_set(v___f_2077_, 3, v_inst_2068_);
    crate::leanh::lean_closure_set(v___f_2077_, 4, v_inst_2069_);
    crate::leanh::lean_closure_set(v___f_2077_, 5, v_toBind_2072_);
    crate::leanh::lean_closure_set(v___f_2077_, 6, v___f_2076_);
    v___x_2078_ = crate::leanh::lean_apply_4(
        v_toBind_2072_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2073_,
        v___f_2077_,
    );
    return v___x_2078_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn(
    mut v_m_2079_: *mut crate::leanh::LeanObject,
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
    mut v_inst_2081_: *mut crate::leanh::LeanObject,
    mut v_inst_2082_: *mut crate::leanh::LeanObject,
    mut v_inst_2083_: *mut crate::leanh::LeanObject,
    mut v_inst_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(
        v_inst_2080_,
        v_inst_2081_,
        v_inst_2082_,
        v_inst_2083_,
        v_inst_2084_,
    );
    return v___x_2085_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(
    mut v_subFn_2086_: *mut crate::leanh::LeanObject,
    mut v_s_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_unused_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2088_ = crate::leanh::lean_ctor_get(v_s_2087_, 0);
                v_type_2089_ = crate::leanh::lean_ctor_get(v_s_2087_, 1);
                v_u_2090_ = crate::leanh::lean_ctor_get(v_s_2087_, 2);
                v_ringInst_2091_ = crate::leanh::lean_ctor_get(v_s_2087_, 3);
                v_semiringInst_2092_ = crate::leanh::lean_ctor_get(v_s_2087_, 4);
                v_charInst_x3f_2093_ = crate::leanh::lean_ctor_get(v_s_2087_, 5);
                v_addFn_x3f_2094_ = crate::leanh::lean_ctor_get(v_s_2087_, 6);
                v_mulFn_x3f_2095_ = crate::leanh::lean_ctor_get(v_s_2087_, 7);
                v_negFn_x3f_2096_ = crate::leanh::lean_ctor_get(v_s_2087_, 9);
                v_powFn_x3f_2097_ = crate::leanh::lean_ctor_get(v_s_2087_, 10);
                v_intCastFn_x3f_2098_ = crate::leanh::lean_ctor_get(v_s_2087_, 11);
                v_natCastFn_x3f_2099_ = crate::leanh::lean_ctor_get(v_s_2087_, 12);
                v_one_x3f_2100_ = crate::leanh::lean_ctor_get(v_s_2087_, 13);
                v_isSharedCheck_2108_ = (!crate::leanh::lean_is_exclusive(v_s_2087_)) as u8;
                if v_isSharedCheck_2108_ == 0 {
                    v_unused_2109_ = crate::leanh::lean_ctor_get(v_s_2087_, 8);
                    crate::leanh::lean_dec(v_unused_2109_);
                    v___x_2102_ = v_s_2087_;
                    v_isShared_2103_ = v_isSharedCheck_2108_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_one_x3f_2100_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2099_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2098_);
                    crate::leanh::lean_inc(v_powFn_x3f_2097_);
                    crate::leanh::lean_inc(v_negFn_x3f_2096_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2095_);
                    crate::leanh::lean_inc(v_addFn_x3f_2094_);
                    crate::leanh::lean_inc(v_charInst_x3f_2093_);
                    crate::leanh::lean_inc(v_semiringInst_2092_);
                    crate::leanh::lean_inc(v_ringInst_2091_);
                    crate::leanh::lean_inc(v_u_2090_);
                    crate::leanh::lean_inc(v_type_2089_);
                    crate::leanh::lean_inc(v_id_2088_);
                    crate::leanh::lean_dec(v_s_2087_);
                    v___x_2102_ = crate::leanh::lean_box(0);
                    v_isShared_2103_ = v_isSharedCheck_2108_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2104_, 0, v_subFn_2086_);
                if v_isShared_2103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2102_, 8, v___x_2104_);
                    v___x_2106_ = v___x_2102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_id_2088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_type_2089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_u_2090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_ringInst_2091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 4, v_semiringInst_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 5, v_charInst_x3f_2093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 6, v_addFn_x3f_2094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 7, v_mulFn_x3f_2095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 8, v___x_2104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 9, v_negFn_x3f_2096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 10, v_powFn_x3f_2097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 11, v_intCastFn_x3f_2098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 12, v_natCastFn_x3f_2099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 13, v_one_x3f_2100_);
                    v___x_2106_ = v_reuseFailAlloc_2107_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(
    mut v_toPure_2110_: *mut crate::leanh::LeanObject,
    mut v_subFn_2111_: *mut crate::leanh::LeanObject,
    mut v_____r_2112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2113_ =
        crate::leanh::lean_apply_2(v_toPure_2110_, crate::leanh::lean_box(0), v_subFn_2111_);
    return v___x_2113_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(
    mut v_toPure_2114_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2115_: *mut crate::leanh::LeanObject,
    mut v_toBind_2116_: *mut crate::leanh::LeanObject,
    mut v_subFn_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_subFn_2117_);
    v___f_2118_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2118_, 0, v_subFn_2117_);
    v___f_2119_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2119_, 0, v_toPure_2114_);
    crate::leanh::lean_closure_set(v___f_2119_, 1, v_subFn_2117_);
    v___x_2120_ = crate::leanh::lean_apply_1(v_modifyRing_2115_, v___f_2118_);
    v___x_2121_ = crate::leanh::lean_apply_4(
        v_toBind_2116_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2120_,
        v___f_2119_,
    );
    return v___x_2121_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(
    mut v_toPure_2139_: *mut crate::leanh::LeanObject,
    mut v_inst_2140_: *mut crate::leanh::LeanObject,
    mut v_inst_2141_: *mut crate::leanh::LeanObject,
    mut v_inst_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_toBind_2144_: *mut crate::leanh::LeanObject,
    mut v___f_2145_: *mut crate::leanh::LeanObject,
    mut v_ring_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subFn_x3f_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_subFn_x3f_2147_ = crate::leanh::lean_ctor_get(v_ring_2146_, 8);
    if crate::leanh::lean_obj_tag(v_subFn_x3f_2147_) == 1 {
        let mut v_val_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_subFn_x3f_2147_);
        crate::leanh::lean_dec_ref(v_ring_2146_);
        crate::leanh::lean_dec(v___f_2145_);
        crate::leanh::lean_dec(v_toBind_2144_);
        crate::leanh::lean_dec_ref(v_inst_2143_);
        crate::leanh::lean_dec_ref(v_inst_2142_);
        crate::leanh::lean_dec_ref(v_inst_2141_);
        crate::leanh::lean_dec(v_inst_2140_);
        v_val_2148_ = crate::leanh::lean_ctor_get(v_subFn_x3f_2147_, 0);
        crate::leanh::lean_inc(v_val_2148_);
        crate::leanh::lean_dec_ref_known(v_subFn_x3f_2147_, 1);
        v___x_2149_ =
            crate::leanh::lean_apply_2(v_toPure_2139_, crate::leanh::lean_box(0), v_val_2148_);
        return v___x_2149_;
    } else {
        let mut v_type_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ringInst_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2139_);
        v_type_2150_ = crate::leanh::lean_ctor_get(v_ring_2146_, 1);
        crate::leanh::lean_inc_ref_n(v_type_2150_, 3);
        v_u_2151_ = crate::leanh::lean_ctor_get(v_ring_2146_, 2);
        crate::leanh::lean_inc_n(v_u_2151_, 2);
        v_ringInst_2152_ = crate::leanh::lean_ctor_get(v_ring_2146_, 3);
        crate::leanh::lean_inc_ref(v_ringInst_2152_);
        crate::leanh::lean_dec_ref(v_ring_2146_);
        v___x_2153_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1;
        v___x_2154_ = crate::leanh::lean_box(0);
        v___x_2155_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2155_, 0, v_u_2151_);
        crate::leanh::lean_ctor_set(v___x_2155_, 1, v___x_2154_);
        crate::leanh::lean_inc_ref(v___x_2155_);
        v___x_2156_ = l_Lean_mkConst(v___x_2153_, v___x_2155_);
        v___x_2157_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4;
        v___x_2158_ = l_Lean_mkConst(v___x_2157_, v___x_2155_);
        v___x_2159_ = l_Lean_mkAppB(v___x_2158_, v_type_2150_, v_ringInst_2152_);
        v_expectedInst_2160_ = l_Lean_mkAppB(v___x_2156_, v_type_2150_, v___x_2159_);
        v___x_2161_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6;
        v___x_2162_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8;
        v___x_2163_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
                v_inst_2140_,
                v_inst_2141_,
                v_inst_2142_,
                v_inst_2143_,
                v_type_2150_,
                v_u_2151_,
                v___x_2161_,
                v___x_2162_,
                v_expectedInst_2160_,
            );
        v___x_2164_ = crate::leanh::lean_apply_4(
            v_toBind_2144_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2163_,
            v___f_2145_,
        );
        return v___x_2164_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg(
    mut v_inst_2165_: *mut crate::leanh::LeanObject,
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
    mut v_inst_2167_: *mut crate::leanh::LeanObject,
    mut v_inst_2168_: *mut crate::leanh::LeanObject,
    mut v_inst_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2170_ = crate::leanh::lean_ctor_get(v_inst_2167_, 0);
    v_toBind_2171_ = crate::leanh::lean_ctor_get(v_inst_2167_, 1);
    crate::leanh::lean_inc_n(v_toBind_2171_, 3);
    v_getRing_2172_ = crate::leanh::lean_ctor_get(v_inst_2169_, 0);
    crate::leanh::lean_inc(v_getRing_2172_);
    v_modifyRing_2173_ = crate::leanh::lean_ctor_get(v_inst_2169_, 1);
    crate::leanh::lean_inc(v_modifyRing_2173_);
    crate::leanh::lean_dec_ref(v_inst_2169_);
    v_toPure_2174_ = crate::leanh::lean_ctor_get(v_toApplicative_2170_, 1);
    crate::leanh::lean_inc_n(v_toPure_2174_, 2);
    v___f_2175_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2175_, 0, v_toPure_2174_);
    crate::leanh::lean_closure_set(v___f_2175_, 1, v_modifyRing_2173_);
    crate::leanh::lean_closure_set(v___f_2175_, 2, v_toBind_2171_);
    v___f_2176_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2176_, 0, v_toPure_2174_);
    crate::leanh::lean_closure_set(v___f_2176_, 1, v_inst_2165_);
    crate::leanh::lean_closure_set(v___f_2176_, 2, v_inst_2166_);
    crate::leanh::lean_closure_set(v___f_2176_, 3, v_inst_2167_);
    crate::leanh::lean_closure_set(v___f_2176_, 4, v_inst_2168_);
    crate::leanh::lean_closure_set(v___f_2176_, 5, v_toBind_2171_);
    crate::leanh::lean_closure_set(v___f_2176_, 6, v___f_2175_);
    v___x_2177_ = crate::leanh::lean_apply_4(
        v_toBind_2171_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2172_,
        v___f_2176_,
    );
    return v___x_2177_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn(
    mut v_m_2178_: *mut crate::leanh::LeanObject,
    mut v_inst_2179_: *mut crate::leanh::LeanObject,
    mut v_inst_2180_: *mut crate::leanh::LeanObject,
    mut v_inst_2181_: *mut crate::leanh::LeanObject,
    mut v_inst_2182_: *mut crate::leanh::LeanObject,
    mut v_inst_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2184_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(
        v_inst_2179_,
        v_inst_2180_,
        v_inst_2181_,
        v_inst_2182_,
        v_inst_2183_,
    );
    return v___x_2184_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(
    mut v_negFn_2185_: *mut crate::leanh::LeanObject,
    mut v_s_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_unused_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2187_ = crate::leanh::lean_ctor_get(v_s_2186_, 0);
                v_type_2188_ = crate::leanh::lean_ctor_get(v_s_2186_, 1);
                v_u_2189_ = crate::leanh::lean_ctor_get(v_s_2186_, 2);
                v_ringInst_2190_ = crate::leanh::lean_ctor_get(v_s_2186_, 3);
                v_semiringInst_2191_ = crate::leanh::lean_ctor_get(v_s_2186_, 4);
                v_charInst_x3f_2192_ = crate::leanh::lean_ctor_get(v_s_2186_, 5);
                v_addFn_x3f_2193_ = crate::leanh::lean_ctor_get(v_s_2186_, 6);
                v_mulFn_x3f_2194_ = crate::leanh::lean_ctor_get(v_s_2186_, 7);
                v_subFn_x3f_2195_ = crate::leanh::lean_ctor_get(v_s_2186_, 8);
                v_powFn_x3f_2196_ = crate::leanh::lean_ctor_get(v_s_2186_, 10);
                v_intCastFn_x3f_2197_ = crate::leanh::lean_ctor_get(v_s_2186_, 11);
                v_natCastFn_x3f_2198_ = crate::leanh::lean_ctor_get(v_s_2186_, 12);
                v_one_x3f_2199_ = crate::leanh::lean_ctor_get(v_s_2186_, 13);
                v_isSharedCheck_2207_ = (!crate::leanh::lean_is_exclusive(v_s_2186_)) as u8;
                if v_isSharedCheck_2207_ == 0 {
                    v_unused_2208_ = crate::leanh::lean_ctor_get(v_s_2186_, 9);
                    crate::leanh::lean_dec(v_unused_2208_);
                    v___x_2201_ = v_s_2186_;
                    v_isShared_2202_ = v_isSharedCheck_2207_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_one_x3f_2199_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2198_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2197_);
                    crate::leanh::lean_inc(v_powFn_x3f_2196_);
                    crate::leanh::lean_inc(v_subFn_x3f_2195_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2194_);
                    crate::leanh::lean_inc(v_addFn_x3f_2193_);
                    crate::leanh::lean_inc(v_charInst_x3f_2192_);
                    crate::leanh::lean_inc(v_semiringInst_2191_);
                    crate::leanh::lean_inc(v_ringInst_2190_);
                    crate::leanh::lean_inc(v_u_2189_);
                    crate::leanh::lean_inc(v_type_2188_);
                    crate::leanh::lean_inc(v_id_2187_);
                    crate::leanh::lean_dec(v_s_2186_);
                    v___x_2201_ = crate::leanh::lean_box(0);
                    v_isShared_2202_ = v_isSharedCheck_2207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2203_, 0, v_negFn_2185_);
                if v_isShared_2202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2201_, 9, v___x_2203_);
                    v___x_2205_ = v___x_2201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_id_2187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_type_2188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_u_2189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_ringInst_2190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_semiringInst_2191_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 5, v_charInst_x3f_2192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 6, v_addFn_x3f_2193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 7, v_mulFn_x3f_2194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 8, v_subFn_x3f_2195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 9, v___x_2203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 10, v_powFn_x3f_2196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 11, v_intCastFn_x3f_2197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 12, v_natCastFn_x3f_2198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 13, v_one_x3f_2199_);
                    v___x_2205_ = v_reuseFailAlloc_2206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(
    mut v_toPure_2209_: *mut crate::leanh::LeanObject,
    mut v_negFn_2210_: *mut crate::leanh::LeanObject,
    mut v_____r_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2212_ =
        crate::leanh::lean_apply_2(v_toPure_2209_, crate::leanh::lean_box(0), v_negFn_2210_);
    return v___x_2212_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(
    mut v_toPure_2213_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2214_: *mut crate::leanh::LeanObject,
    mut v_toBind_2215_: *mut crate::leanh::LeanObject,
    mut v_negFn_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_negFn_2216_);
    v___f_2217_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2217_, 0, v_negFn_2216_);
    v___f_2218_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2218_, 0, v_toPure_2213_);
    crate::leanh::lean_closure_set(v___f_2218_, 1, v_negFn_2216_);
    v___x_2219_ = crate::leanh::lean_apply_1(v_modifyRing_2214_, v___f_2217_);
    v___x_2220_ = crate::leanh::lean_apply_4(
        v_toBind_2215_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2219_,
        v___f_2218_,
    );
    return v___x_2220_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(
    mut v_toPure_2234_: *mut crate::leanh::LeanObject,
    mut v_inst_2235_: *mut crate::leanh::LeanObject,
    mut v_inst_2236_: *mut crate::leanh::LeanObject,
    mut v_inst_2237_: *mut crate::leanh::LeanObject,
    mut v_inst_2238_: *mut crate::leanh::LeanObject,
    mut v_toBind_2239_: *mut crate::leanh::LeanObject,
    mut v___f_2240_: *mut crate::leanh::LeanObject,
    mut v_ring_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_negFn_x3f_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_negFn_x3f_2242_ = crate::leanh::lean_ctor_get(v_ring_2241_, 9);
    if crate::leanh::lean_obj_tag(v_negFn_x3f_2242_) == 1 {
        let mut v_val_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_negFn_x3f_2242_);
        crate::leanh::lean_dec_ref(v_ring_2241_);
        crate::leanh::lean_dec(v___f_2240_);
        crate::leanh::lean_dec(v_toBind_2239_);
        crate::leanh::lean_dec_ref(v_inst_2238_);
        crate::leanh::lean_dec_ref(v_inst_2237_);
        crate::leanh::lean_dec_ref(v_inst_2236_);
        crate::leanh::lean_dec(v_inst_2235_);
        v_val_2243_ = crate::leanh::lean_ctor_get(v_negFn_x3f_2242_, 0);
        crate::leanh::lean_inc(v_val_2243_);
        crate::leanh::lean_dec_ref_known(v_negFn_x3f_2242_, 1);
        v___x_2244_ =
            crate::leanh::lean_apply_2(v_toPure_2234_, crate::leanh::lean_box(0), v_val_2243_);
        return v___x_2244_;
    } else {
        let mut v_type_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ringInst_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2234_);
        v_type_2245_ = crate::leanh::lean_ctor_get(v_ring_2241_, 1);
        crate::leanh::lean_inc_ref_n(v_type_2245_, 2);
        v_u_2246_ = crate::leanh::lean_ctor_get(v_ring_2241_, 2);
        crate::leanh::lean_inc_n(v_u_2246_, 2);
        v_ringInst_2247_ = crate::leanh::lean_ctor_get(v_ring_2241_, 3);
        crate::leanh::lean_inc_ref(v_ringInst_2247_);
        crate::leanh::lean_dec_ref(v_ring_2241_);
        v___x_2248_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1;
        v___x_2249_ = crate::leanh::lean_box(0);
        v___x_2250_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2250_, 0, v_u_2246_);
        crate::leanh::lean_ctor_set(v___x_2250_, 1, v___x_2249_);
        v___x_2251_ = l_Lean_mkConst(v___x_2248_, v___x_2250_);
        v_expectedInst_2252_ = l_Lean_mkAppB(v___x_2251_, v_type_2245_, v_ringInst_2247_);
        v___x_2253_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3;
        v___x_2254_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5;
        v___x_2255_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(
                v_inst_2235_,
                v_inst_2236_,
                v_inst_2237_,
                v_inst_2238_,
                v_type_2245_,
                v_u_2246_,
                v___x_2253_,
                v___x_2254_,
                v_expectedInst_2252_,
            );
        v___x_2256_ = crate::leanh::lean_apply_4(
            v_toBind_2239_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2255_,
            v___f_2240_,
        );
        return v___x_2256_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg(
    mut v_inst_2257_: *mut crate::leanh::LeanObject,
    mut v_inst_2258_: *mut crate::leanh::LeanObject,
    mut v_inst_2259_: *mut crate::leanh::LeanObject,
    mut v_inst_2260_: *mut crate::leanh::LeanObject,
    mut v_inst_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2262_ = crate::leanh::lean_ctor_get(v_inst_2259_, 0);
    v_toBind_2263_ = crate::leanh::lean_ctor_get(v_inst_2259_, 1);
    crate::leanh::lean_inc_n(v_toBind_2263_, 3);
    v_getRing_2264_ = crate::leanh::lean_ctor_get(v_inst_2261_, 0);
    crate::leanh::lean_inc(v_getRing_2264_);
    v_modifyRing_2265_ = crate::leanh::lean_ctor_get(v_inst_2261_, 1);
    crate::leanh::lean_inc(v_modifyRing_2265_);
    crate::leanh::lean_dec_ref(v_inst_2261_);
    v_toPure_2266_ = crate::leanh::lean_ctor_get(v_toApplicative_2262_, 1);
    crate::leanh::lean_inc_n(v_toPure_2266_, 2);
    v___f_2267_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2267_, 0, v_toPure_2266_);
    crate::leanh::lean_closure_set(v___f_2267_, 1, v_modifyRing_2265_);
    crate::leanh::lean_closure_set(v___f_2267_, 2, v_toBind_2263_);
    v___f_2268_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2268_, 0, v_toPure_2266_);
    crate::leanh::lean_closure_set(v___f_2268_, 1, v_inst_2257_);
    crate::leanh::lean_closure_set(v___f_2268_, 2, v_inst_2258_);
    crate::leanh::lean_closure_set(v___f_2268_, 3, v_inst_2259_);
    crate::leanh::lean_closure_set(v___f_2268_, 4, v_inst_2260_);
    crate::leanh::lean_closure_set(v___f_2268_, 5, v_toBind_2263_);
    crate::leanh::lean_closure_set(v___f_2268_, 6, v___f_2267_);
    v___x_2269_ = crate::leanh::lean_apply_4(
        v_toBind_2263_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2264_,
        v___f_2268_,
    );
    return v___x_2269_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn(
    mut v_m_2270_: *mut crate::leanh::LeanObject,
    mut v_inst_2271_: *mut crate::leanh::LeanObject,
    mut v_inst_2272_: *mut crate::leanh::LeanObject,
    mut v_inst_2273_: *mut crate::leanh::LeanObject,
    mut v_inst_2274_: *mut crate::leanh::LeanObject,
    mut v_inst_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(
        v_inst_2271_,
        v_inst_2272_,
        v_inst_2273_,
        v_inst_2274_,
        v_inst_2275_,
    );
    return v___x_2276_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(
    mut v_powFn_2277_: *mut crate::leanh::LeanObject,
    mut v_s_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2279_ = crate::leanh::lean_ctor_get(v_s_2278_, 0);
                v_type_2280_ = crate::leanh::lean_ctor_get(v_s_2278_, 1);
                v_u_2281_ = crate::leanh::lean_ctor_get(v_s_2278_, 2);
                v_ringInst_2282_ = crate::leanh::lean_ctor_get(v_s_2278_, 3);
                v_semiringInst_2283_ = crate::leanh::lean_ctor_get(v_s_2278_, 4);
                v_charInst_x3f_2284_ = crate::leanh::lean_ctor_get(v_s_2278_, 5);
                v_addFn_x3f_2285_ = crate::leanh::lean_ctor_get(v_s_2278_, 6);
                v_mulFn_x3f_2286_ = crate::leanh::lean_ctor_get(v_s_2278_, 7);
                v_subFn_x3f_2287_ = crate::leanh::lean_ctor_get(v_s_2278_, 8);
                v_negFn_x3f_2288_ = crate::leanh::lean_ctor_get(v_s_2278_, 9);
                v_intCastFn_x3f_2289_ = crate::leanh::lean_ctor_get(v_s_2278_, 11);
                v_natCastFn_x3f_2290_ = crate::leanh::lean_ctor_get(v_s_2278_, 12);
                v_one_x3f_2291_ = crate::leanh::lean_ctor_get(v_s_2278_, 13);
                v_isSharedCheck_2299_ = (!crate::leanh::lean_is_exclusive(v_s_2278_)) as u8;
                if v_isSharedCheck_2299_ == 0 {
                    v_unused_2300_ = crate::leanh::lean_ctor_get(v_s_2278_, 10);
                    crate::leanh::lean_dec(v_unused_2300_);
                    v___x_2293_ = v_s_2278_;
                    v_isShared_2294_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_one_x3f_2291_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2290_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2289_);
                    crate::leanh::lean_inc(v_negFn_x3f_2288_);
                    crate::leanh::lean_inc(v_subFn_x3f_2287_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2286_);
                    crate::leanh::lean_inc(v_addFn_x3f_2285_);
                    crate::leanh::lean_inc(v_charInst_x3f_2284_);
                    crate::leanh::lean_inc(v_semiringInst_2283_);
                    crate::leanh::lean_inc(v_ringInst_2282_);
                    crate::leanh::lean_inc(v_u_2281_);
                    crate::leanh::lean_inc(v_type_2280_);
                    crate::leanh::lean_inc(v_id_2279_);
                    crate::leanh::lean_dec(v_s_2278_);
                    v___x_2293_ = crate::leanh::lean_box(0);
                    v_isShared_2294_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2295_, 0, v_powFn_2277_);
                if v_isShared_2294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2293_, 10, v___x_2295_);
                    v___x_2297_ = v___x_2293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_id_2279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_type_2280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_u_2281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 3, v_ringInst_2282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 4, v_semiringInst_2283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 5, v_charInst_x3f_2284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 6, v_addFn_x3f_2285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 7, v_mulFn_x3f_2286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 8, v_subFn_x3f_2287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 9, v_negFn_x3f_2288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 10, v___x_2295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 11, v_intCastFn_x3f_2289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 12, v_natCastFn_x3f_2290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 13, v_one_x3f_2291_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(
    mut v_toPure_2301_: *mut crate::leanh::LeanObject,
    mut v_powFn_2302_: *mut crate::leanh::LeanObject,
    mut v_____r_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ =
        crate::leanh::lean_apply_2(v_toPure_2301_, crate::leanh::lean_box(0), v_powFn_2302_);
    return v___x_2304_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(
    mut v_toPure_2305_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2306_: *mut crate::leanh::LeanObject,
    mut v_toBind_2307_: *mut crate::leanh::LeanObject,
    mut v_powFn_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_powFn_2308_);
    v___f_2309_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2309_, 0, v_powFn_2308_);
    v___f_2310_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2310_, 0, v_toPure_2305_);
    crate::leanh::lean_closure_set(v___f_2310_, 1, v_powFn_2308_);
    v___x_2311_ = crate::leanh::lean_apply_1(v_modifyRing_2306_, v___f_2309_);
    v___x_2312_ = crate::leanh::lean_apply_4(
        v_toBind_2307_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2311_,
        v___f_2310_,
    );
    return v___x_2312_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(
    mut v_toPure_2313_: *mut crate::leanh::LeanObject,
    mut v_inst_2314_: *mut crate::leanh::LeanObject,
    mut v_inst_2315_: *mut crate::leanh::LeanObject,
    mut v_inst_2316_: *mut crate::leanh::LeanObject,
    mut v_inst_2317_: *mut crate::leanh::LeanObject,
    mut v_toBind_2318_: *mut crate::leanh::LeanObject,
    mut v___f_2319_: *mut crate::leanh::LeanObject,
    mut v_ring_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_powFn_x3f_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_powFn_x3f_2321_ = crate::leanh::lean_ctor_get(v_ring_2320_, 10);
    if crate::leanh::lean_obj_tag(v_powFn_x3f_2321_) == 1 {
        let mut v_val_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_powFn_x3f_2321_);
        crate::leanh::lean_dec_ref(v_ring_2320_);
        crate::leanh::lean_dec(v___f_2319_);
        crate::leanh::lean_dec(v_toBind_2318_);
        crate::leanh::lean_dec_ref(v_inst_2317_);
        crate::leanh::lean_dec_ref(v_inst_2316_);
        crate::leanh::lean_dec_ref(v_inst_2315_);
        crate::leanh::lean_dec(v_inst_2314_);
        v_val_2322_ = crate::leanh::lean_ctor_get(v_powFn_x3f_2321_, 0);
        crate::leanh::lean_inc(v_val_2322_);
        crate::leanh::lean_dec_ref_known(v_powFn_x3f_2321_, 1);
        v___x_2323_ =
            crate::leanh::lean_apply_2(v_toPure_2313_, crate::leanh::lean_box(0), v_val_2322_);
        return v___x_2323_;
    } else {
        let mut v_type_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2313_);
        v_type_2324_ = crate::leanh::lean_ctor_get(v_ring_2320_, 1);
        crate::leanh::lean_inc_ref(v_type_2324_);
        v_u_2325_ = crate::leanh::lean_ctor_get(v_ring_2320_, 2);
        crate::leanh::lean_inc(v_u_2325_);
        v_semiringInst_2326_ = crate::leanh::lean_ctor_get(v_ring_2320_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_2326_);
        crate::leanh::lean_dec_ref(v_ring_2320_);
        v___x_2327_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(
                v_inst_2314_,
                v_inst_2315_,
                v_inst_2316_,
                v_inst_2317_,
                v_u_2325_,
                v_type_2324_,
                v_semiringInst_2326_,
            );
        v___x_2328_ = crate::leanh::lean_apply_4(
            v_toBind_2318_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2327_,
            v___f_2319_,
        );
        return v___x_2328_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg(
    mut v_inst_2329_: *mut crate::leanh::LeanObject,
    mut v_inst_2330_: *mut crate::leanh::LeanObject,
    mut v_inst_2331_: *mut crate::leanh::LeanObject,
    mut v_inst_2332_: *mut crate::leanh::LeanObject,
    mut v_inst_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2334_ = crate::leanh::lean_ctor_get(v_inst_2331_, 0);
    v_toBind_2335_ = crate::leanh::lean_ctor_get(v_inst_2331_, 1);
    crate::leanh::lean_inc_n(v_toBind_2335_, 3);
    v_getRing_2336_ = crate::leanh::lean_ctor_get(v_inst_2333_, 0);
    crate::leanh::lean_inc(v_getRing_2336_);
    v_modifyRing_2337_ = crate::leanh::lean_ctor_get(v_inst_2333_, 1);
    crate::leanh::lean_inc(v_modifyRing_2337_);
    crate::leanh::lean_dec_ref(v_inst_2333_);
    v_toPure_2338_ = crate::leanh::lean_ctor_get(v_toApplicative_2334_, 1);
    crate::leanh::lean_inc_n(v_toPure_2338_, 2);
    v___f_2339_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2339_, 0, v_toPure_2338_);
    crate::leanh::lean_closure_set(v___f_2339_, 1, v_modifyRing_2337_);
    crate::leanh::lean_closure_set(v___f_2339_, 2, v_toBind_2335_);
    v___f_2340_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2340_, 0, v_toPure_2338_);
    crate::leanh::lean_closure_set(v___f_2340_, 1, v_inst_2329_);
    crate::leanh::lean_closure_set(v___f_2340_, 2, v_inst_2330_);
    crate::leanh::lean_closure_set(v___f_2340_, 3, v_inst_2331_);
    crate::leanh::lean_closure_set(v___f_2340_, 4, v_inst_2332_);
    crate::leanh::lean_closure_set(v___f_2340_, 5, v_toBind_2335_);
    crate::leanh::lean_closure_set(v___f_2340_, 6, v___f_2339_);
    v___x_2341_ = crate::leanh::lean_apply_4(
        v_toBind_2335_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2336_,
        v___f_2340_,
    );
    return v___x_2341_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn(
    mut v_m_2342_: *mut crate::leanh::LeanObject,
    mut v_inst_2343_: *mut crate::leanh::LeanObject,
    mut v_inst_2344_: *mut crate::leanh::LeanObject,
    mut v_inst_2345_: *mut crate::leanh::LeanObject,
    mut v_inst_2346_: *mut crate::leanh::LeanObject,
    mut v_inst_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(
        v_inst_2343_,
        v_inst_2344_,
        v_inst_2345_,
        v_inst_2346_,
        v_inst_2347_,
    );
    return v___x_2348_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(
    mut v_intCastFn_2349_: *mut crate::leanh::LeanObject,
    mut v_s_2350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_unused_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2351_ = crate::leanh::lean_ctor_get(v_s_2350_, 0);
                v_type_2352_ = crate::leanh::lean_ctor_get(v_s_2350_, 1);
                v_u_2353_ = crate::leanh::lean_ctor_get(v_s_2350_, 2);
                v_ringInst_2354_ = crate::leanh::lean_ctor_get(v_s_2350_, 3);
                v_semiringInst_2355_ = crate::leanh::lean_ctor_get(v_s_2350_, 4);
                v_charInst_x3f_2356_ = crate::leanh::lean_ctor_get(v_s_2350_, 5);
                v_addFn_x3f_2357_ = crate::leanh::lean_ctor_get(v_s_2350_, 6);
                v_mulFn_x3f_2358_ = crate::leanh::lean_ctor_get(v_s_2350_, 7);
                v_subFn_x3f_2359_ = crate::leanh::lean_ctor_get(v_s_2350_, 8);
                v_negFn_x3f_2360_ = crate::leanh::lean_ctor_get(v_s_2350_, 9);
                v_powFn_x3f_2361_ = crate::leanh::lean_ctor_get(v_s_2350_, 10);
                v_natCastFn_x3f_2362_ = crate::leanh::lean_ctor_get(v_s_2350_, 12);
                v_one_x3f_2363_ = crate::leanh::lean_ctor_get(v_s_2350_, 13);
                v_isSharedCheck_2371_ = (!crate::leanh::lean_is_exclusive(v_s_2350_)) as u8;
                if v_isSharedCheck_2371_ == 0 {
                    v_unused_2372_ = crate::leanh::lean_ctor_get(v_s_2350_, 11);
                    crate::leanh::lean_dec(v_unused_2372_);
                    v___x_2365_ = v_s_2350_;
                    v_isShared_2366_ = v_isSharedCheck_2371_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_one_x3f_2363_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2362_);
                    crate::leanh::lean_inc(v_powFn_x3f_2361_);
                    crate::leanh::lean_inc(v_negFn_x3f_2360_);
                    crate::leanh::lean_inc(v_subFn_x3f_2359_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2358_);
                    crate::leanh::lean_inc(v_addFn_x3f_2357_);
                    crate::leanh::lean_inc(v_charInst_x3f_2356_);
                    crate::leanh::lean_inc(v_semiringInst_2355_);
                    crate::leanh::lean_inc(v_ringInst_2354_);
                    crate::leanh::lean_inc(v_u_2353_);
                    crate::leanh::lean_inc(v_type_2352_);
                    crate::leanh::lean_inc(v_id_2351_);
                    crate::leanh::lean_dec(v_s_2350_);
                    v___x_2365_ = crate::leanh::lean_box(0);
                    v_isShared_2366_ = v_isSharedCheck_2371_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2367_, 0, v_intCastFn_2349_);
                if v_isShared_2366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2365_, 11, v___x_2367_);
                    v___x_2369_ = v___x_2365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_id_2351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_type_2352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_u_2353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_ringInst_2354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_semiringInst_2355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 5, v_charInst_x3f_2356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 6, v_addFn_x3f_2357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 7, v_mulFn_x3f_2358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 8, v_subFn_x3f_2359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 9, v_negFn_x3f_2360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 10, v_powFn_x3f_2361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 11, v___x_2367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 12, v_natCastFn_x3f_2362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 13, v_one_x3f_2363_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(
    mut v_toPure_2373_: *mut crate::leanh::LeanObject,
    mut v_intCastFn_2374_: *mut crate::leanh::LeanObject,
    mut v_____r_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ =
        crate::leanh::lean_apply_2(v_toPure_2373_, crate::leanh::lean_box(0), v_intCastFn_2374_);
    return v___x_2376_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(
    mut v_toPure_2377_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2378_: *mut crate::leanh::LeanObject,
    mut v_toBind_2379_: *mut crate::leanh::LeanObject,
    mut v_intCastFn_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_intCastFn_2380_);
    v___f_2381_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2381_, 0, v_intCastFn_2380_);
    v___f_2382_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2382_, 0, v_toPure_2377_);
    crate::leanh::lean_closure_set(v___f_2382_, 1, v_intCastFn_2380_);
    v___x_2383_ = crate::leanh::lean_apply_1(v_modifyRing_2378_, v___f_2381_);
    v___x_2384_ = crate::leanh::lean_apply_4(
        v_toBind_2379_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2383_,
        v___f_2382_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(
    mut v___x_2385_: *mut crate::leanh::LeanObject,
    mut v___x_2386_: *mut crate::leanh::LeanObject,
    mut v___x_2387_: *mut crate::leanh::LeanObject,
    mut v_type_2388_: *mut crate::leanh::LeanObject,
    mut v_canonExpr_2389_: *mut crate::leanh::LeanObject,
    mut v_toBind_2390_: *mut crate::leanh::LeanObject,
    mut v___f_2391_: *mut crate::leanh::LeanObject,
    mut v_inst_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Lean_Name_mkStr2(v___x_2385_, v___x_2386_);
    v___x_2394_ = l_Lean_mkConst(v___x_2393_, v___x_2387_);
    v___x_2395_ = l_Lean_mkAppB(v___x_2394_, v_type_2388_, v_inst_2392_);
    v___x_2396_ = crate::leanh::lean_apply_1(v_canonExpr_2389_, v___x_2395_);
    v___x_2397_ = crate::leanh::lean_apply_4(
        v_toBind_2390_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2396_,
        v___f_2391_,
    );
    return v___x_2397_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(
    mut v_toPure_2403_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_2404_: *mut crate::leanh::LeanObject,
    mut v_toBind_2405_: *mut crate::leanh::LeanObject,
    mut v___f_2406_: *mut crate::leanh::LeanObject,
    mut v___f_2407_: *mut crate::leanh::LeanObject,
    mut v_inst_2408_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2409_) == 0 {
        let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_2408_);
        crate::leanh::lean_dec(v___f_2407_);
        v___x_2410_ =
            crate::leanh::lean_apply_2(v_toPure_2403_, crate::leanh::lean_box(0), v_inst_x27_2404_);
        v___x_2411_ = crate::leanh::lean_apply_4(
            v_toBind_2405_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2410_,
            v___f_2406_,
        );
        return v___x_2411_;
    } else {
        let mut v_val_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2406_);
        v_val_2412_ = crate::leanh::lean_ctor_get(v_____do__lift_2409_, 0);
        crate::leanh::lean_inc_n(v_val_2412_, 2);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2409_, 1);
        crate::leanh::lean_inc(v_toBind_2405_);
        v___f_2413_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_2413_, 0, v_toPure_2403_);
        crate::leanh::lean_closure_set(v___f_2413_, 1, v_val_2412_);
        crate::leanh::lean_closure_set(v___f_2413_, 2, v_toBind_2405_);
        crate::leanh::lean_closure_set(v___f_2413_, 3, v___f_2407_);
        v___x_2414_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2;
        v___x_2415_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
                as *mut core::ffi::c_void,
            8,
            3,
        );
        crate::leanh::lean_closure_set(v___x_2415_, 0, v___x_2414_);
        crate::leanh::lean_closure_set(v___x_2415_, 1, v_val_2412_);
        crate::leanh::lean_closure_set(v___x_2415_, 2, v_inst_x27_2404_);
        v___x_2416_ =
            crate::leanh::lean_apply_2(v_inst_2408_, crate::leanh::lean_box(0), v___x_2415_);
        v___x_2417_ = crate::leanh::lean_apply_4(
            v_toBind_2405_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2416_,
            v___f_2413_,
        );
        return v___x_2417_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(
    mut v_toPure_2427_: *mut crate::leanh::LeanObject,
    mut v_inst_2428_: *mut crate::leanh::LeanObject,
    mut v_toBind_2429_: *mut crate::leanh::LeanObject,
    mut v___f_2430_: *mut crate::leanh::LeanObject,
    mut v_inst_2431_: *mut crate::leanh::LeanObject,
    mut v_ring_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intCastFn_x3f_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instType_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_intCastFn_x3f_2433_ = crate::leanh::lean_ctor_get(v_ring_2432_, 11);
                if crate::leanh::lean_obj_tag(v_intCastFn_x3f_2433_) == 1 {
                    crate::leanh::lean_inc_ref(v_intCastFn_x3f_2433_);
                    crate::leanh::lean_dec_ref(v_ring_2432_);
                    crate::leanh::lean_dec(v_inst_2431_);
                    crate::leanh::lean_dec(v___f_2430_);
                    crate::leanh::lean_dec(v_toBind_2429_);
                    crate::leanh::lean_dec_ref(v_inst_2428_);
                    v_val_2434_ = crate::leanh::lean_ctor_get(v_intCastFn_x3f_2433_, 0);
                    crate::leanh::lean_inc(v_val_2434_);
                    crate::leanh::lean_dec_ref_known(v_intCastFn_x3f_2433_, 1);
                    v___x_2435_ = crate::leanh::lean_apply_2(
                        v_toPure_2427_,
                        crate::leanh::lean_box(0),
                        v_val_2434_,
                    );
                    return v___x_2435_;
                } else {
                    v_type_2436_ = crate::leanh::lean_ctor_get(v_ring_2432_, 1);
                    crate::leanh::lean_inc_ref(v_type_2436_);
                    v_u_2437_ = crate::leanh::lean_ctor_get(v_ring_2432_, 2);
                    crate::leanh::lean_inc(v_u_2437_);
                    v_ringInst_2438_ = crate::leanh::lean_ctor_get(v_ring_2432_, 3);
                    crate::leanh::lean_inc_ref(v_ringInst_2438_);
                    crate::leanh::lean_dec_ref(v_ring_2432_);
                    v_canonExpr_2439_ = crate::leanh::lean_ctor_get(v_inst_2428_, 0);
                    v_synthInstance_x3f_2440_ = crate::leanh::lean_ctor_get(v_inst_2428_, 1);
                    v_isSharedCheck_2461_ = (!crate::leanh::lean_is_exclusive(v_inst_2428_)) as u8;
                    if v_isSharedCheck_2461_ == 0 {
                        v___x_2442_ = v_inst_2428_;
                        v_isShared_2443_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_synthInstance_x3f_2440_);
                        crate::leanh::lean_inc(v_canonExpr_2439_);
                        crate::leanh::lean_dec(v_inst_2428_);
                        v___x_2442_ = crate::leanh::lean_box(0);
                        v_isShared_2443_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2444_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0;
                v___x_2445_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1;
                v___x_2446_ = crate::leanh::lean_box(0);
                if v_isShared_2443_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2442_, 1);
                    crate::leanh::lean_ctor_set(v___x_2442_, 1, v___x_2446_);
                    crate::leanh::lean_ctor_set(v___x_2442_, 0, v_u_2437_);
                    v___x_2448_ = v___x_2442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2460_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_u_2437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2446_);
                    v___x_2448_ = v_reuseFailAlloc_2460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___x_2448_, 2);
                v___x_2449_ = l_Lean_mkConst(v___x_2445_, v___x_2448_);
                crate::leanh::lean_inc_ref_n(v_type_2436_, 2);
                v_inst_x27_2450_ = l_Lean_mkAppB(v___x_2449_, v_type_2436_, v_ringInst_2438_);
                v___x_2451_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2;
                crate::leanh::lean_inc_n(v_toBind_2429_, 2);
                v___f_2452_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3 as *mut core::ffi::c_void,
                    8,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_2452_, 0, v___x_2451_);
                crate::leanh::lean_closure_set(v___f_2452_, 1, v___x_2444_);
                crate::leanh::lean_closure_set(v___f_2452_, 2, v___x_2448_);
                crate::leanh::lean_closure_set(v___f_2452_, 3, v_type_2436_);
                crate::leanh::lean_closure_set(v___f_2452_, 4, v_canonExpr_2439_);
                crate::leanh::lean_closure_set(v___f_2452_, 5, v_toBind_2429_);
                crate::leanh::lean_closure_set(v___f_2452_, 6, v___f_2430_);
                v___f_2453_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_2453_, 0, v___f_2452_);
                crate::leanh::lean_inc_ref(v___f_2453_);
                v___f_2454_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7 as *mut core::ffi::c_void,
                    7,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_2454_, 0, v_toPure_2427_);
                crate::leanh::lean_closure_set(v___f_2454_, 1, v_inst_x27_2450_);
                crate::leanh::lean_closure_set(v___f_2454_, 2, v_toBind_2429_);
                crate::leanh::lean_closure_set(v___f_2454_, 3, v___f_2453_);
                crate::leanh::lean_closure_set(v___f_2454_, 4, v___f_2453_);
                crate::leanh::lean_closure_set(v___f_2454_, 5, v_inst_2431_);
                v___x_2455_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3;
                v___x_2456_ = l_Lean_mkConst(v___x_2455_, v___x_2448_);
                v_instType_2457_ = l_Lean_Expr_app___override(v___x_2456_, v_type_2436_);
                v___x_2458_ =
                    crate::leanh::lean_apply_1(v_synthInstance_x3f_2440_, v_instType_2457_);
                v___x_2459_ = crate::leanh::lean_apply_4(
                    v_toBind_2429_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2458_,
                    v___f_2454_,
                );
                return v___x_2459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(
    mut v_inst_2462_: *mut crate::leanh::LeanObject,
    mut v_inst_2463_: *mut crate::leanh::LeanObject,
    mut v_inst_2464_: *mut crate::leanh::LeanObject,
    mut v_inst_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2466_ = crate::leanh::lean_ctor_get(v_inst_2463_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2466_);
    v_toBind_2467_ = crate::leanh::lean_ctor_get(v_inst_2463_, 1);
    crate::leanh::lean_inc_n(v_toBind_2467_, 3);
    crate::leanh::lean_dec_ref(v_inst_2463_);
    v_getRing_2468_ = crate::leanh::lean_ctor_get(v_inst_2465_, 0);
    crate::leanh::lean_inc(v_getRing_2468_);
    v_modifyRing_2469_ = crate::leanh::lean_ctor_get(v_inst_2465_, 1);
    crate::leanh::lean_inc(v_modifyRing_2469_);
    crate::leanh::lean_dec_ref(v_inst_2465_);
    v_toPure_2470_ = crate::leanh::lean_ctor_get(v_toApplicative_2466_, 1);
    crate::leanh::lean_inc_n(v_toPure_2470_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2466_);
    v___f_2471_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2471_, 0, v_toPure_2470_);
    crate::leanh::lean_closure_set(v___f_2471_, 1, v_modifyRing_2469_);
    crate::leanh::lean_closure_set(v___f_2471_, 2, v_toBind_2467_);
    v___f_2472_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2472_, 0, v_toPure_2470_);
    crate::leanh::lean_closure_set(v___f_2472_, 1, v_inst_2464_);
    crate::leanh::lean_closure_set(v___f_2472_, 2, v_toBind_2467_);
    crate::leanh::lean_closure_set(v___f_2472_, 3, v___f_2471_);
    crate::leanh::lean_closure_set(v___f_2472_, 4, v_inst_2462_);
    v___x_2473_ = crate::leanh::lean_apply_4(
        v_toBind_2467_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2468_,
        v___f_2472_,
    );
    return v___x_2473_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn(
    mut v_m_2474_: *mut crate::leanh::LeanObject,
    mut v_inst_2475_: *mut crate::leanh::LeanObject,
    mut v_inst_2476_: *mut crate::leanh::LeanObject,
    mut v_inst_2477_: *mut crate::leanh::LeanObject,
    mut v_inst_2478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(
        v_inst_2475_,
        v_inst_2476_,
        v_inst_2477_,
        v_inst_2478_,
    );
    return v___x_2479_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(
    mut v_natCastFn_2480_: *mut crate::leanh::LeanObject,
    mut v_s_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2502_: u8 = 0;
    let mut v_unused_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2482_ = crate::leanh::lean_ctor_get(v_s_2481_, 0);
                v_type_2483_ = crate::leanh::lean_ctor_get(v_s_2481_, 1);
                v_u_2484_ = crate::leanh::lean_ctor_get(v_s_2481_, 2);
                v_ringInst_2485_ = crate::leanh::lean_ctor_get(v_s_2481_, 3);
                v_semiringInst_2486_ = crate::leanh::lean_ctor_get(v_s_2481_, 4);
                v_charInst_x3f_2487_ = crate::leanh::lean_ctor_get(v_s_2481_, 5);
                v_addFn_x3f_2488_ = crate::leanh::lean_ctor_get(v_s_2481_, 6);
                v_mulFn_x3f_2489_ = crate::leanh::lean_ctor_get(v_s_2481_, 7);
                v_subFn_x3f_2490_ = crate::leanh::lean_ctor_get(v_s_2481_, 8);
                v_negFn_x3f_2491_ = crate::leanh::lean_ctor_get(v_s_2481_, 9);
                v_powFn_x3f_2492_ = crate::leanh::lean_ctor_get(v_s_2481_, 10);
                v_intCastFn_x3f_2493_ = crate::leanh::lean_ctor_get(v_s_2481_, 11);
                v_one_x3f_2494_ = crate::leanh::lean_ctor_get(v_s_2481_, 13);
                v_isSharedCheck_2502_ = (!crate::leanh::lean_is_exclusive(v_s_2481_)) as u8;
                if v_isSharedCheck_2502_ == 0 {
                    v_unused_2503_ = crate::leanh::lean_ctor_get(v_s_2481_, 12);
                    crate::leanh::lean_dec(v_unused_2503_);
                    v___x_2496_ = v_s_2481_;
                    v_isShared_2497_ = v_isSharedCheck_2502_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_one_x3f_2494_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2493_);
                    crate::leanh::lean_inc(v_powFn_x3f_2492_);
                    crate::leanh::lean_inc(v_negFn_x3f_2491_);
                    crate::leanh::lean_inc(v_subFn_x3f_2490_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2489_);
                    crate::leanh::lean_inc(v_addFn_x3f_2488_);
                    crate::leanh::lean_inc(v_charInst_x3f_2487_);
                    crate::leanh::lean_inc(v_semiringInst_2486_);
                    crate::leanh::lean_inc(v_ringInst_2485_);
                    crate::leanh::lean_inc(v_u_2484_);
                    crate::leanh::lean_inc(v_type_2483_);
                    crate::leanh::lean_inc(v_id_2482_);
                    crate::leanh::lean_dec(v_s_2481_);
                    v___x_2496_ = crate::leanh::lean_box(0);
                    v_isShared_2497_ = v_isSharedCheck_2502_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2498_, 0, v_natCastFn_2480_);
                if v_isShared_2497_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2496_, 12, v___x_2498_);
                    v___x_2500_ = v___x_2496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2501_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_id_2482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_type_2483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_u_2484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_ringInst_2485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_semiringInst_2486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 5, v_charInst_x3f_2487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 6, v_addFn_x3f_2488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 7, v_mulFn_x3f_2489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 8, v_subFn_x3f_2490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 9, v_negFn_x3f_2491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 10, v_powFn_x3f_2492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 11, v_intCastFn_x3f_2493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 12, v___x_2498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 13, v_one_x3f_2494_);
                    v___x_2500_ = v_reuseFailAlloc_2501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(
    mut v_toPure_2504_: *mut crate::leanh::LeanObject,
    mut v_natCastFn_2505_: *mut crate::leanh::LeanObject,
    mut v_____r_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ =
        crate::leanh::lean_apply_2(v_toPure_2504_, crate::leanh::lean_box(0), v_natCastFn_2505_);
    return v___x_2507_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(
    mut v_toPure_2508_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2509_: *mut crate::leanh::LeanObject,
    mut v_toBind_2510_: *mut crate::leanh::LeanObject,
    mut v_natCastFn_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_natCastFn_2511_);
    v___f_2512_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2512_, 0, v_natCastFn_2511_);
    v___f_2513_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2513_, 0, v_toPure_2508_);
    crate::leanh::lean_closure_set(v___f_2513_, 1, v_natCastFn_2511_);
    v___x_2514_ = crate::leanh::lean_apply_1(v_modifyRing_2509_, v___f_2512_);
    v___x_2515_ = crate::leanh::lean_apply_4(
        v_toBind_2510_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2514_,
        v___f_2513_,
    );
    return v___x_2515_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(
    mut v_toPure_2516_: *mut crate::leanh::LeanObject,
    mut v_inst_2517_: *mut crate::leanh::LeanObject,
    mut v_inst_2518_: *mut crate::leanh::LeanObject,
    mut v_inst_2519_: *mut crate::leanh::LeanObject,
    mut v_toBind_2520_: *mut crate::leanh::LeanObject,
    mut v___f_2521_: *mut crate::leanh::LeanObject,
    mut v_ring_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natCastFn_x3f_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_2523_ = crate::leanh::lean_ctor_get(v_ring_2522_, 12);
    if crate::leanh::lean_obj_tag(v_natCastFn_x3f_2523_) == 1 {
        let mut v_val_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_natCastFn_x3f_2523_);
        crate::leanh::lean_dec_ref(v_ring_2522_);
        crate::leanh::lean_dec(v___f_2521_);
        crate::leanh::lean_dec(v_toBind_2520_);
        crate::leanh::lean_dec_ref(v_inst_2519_);
        crate::leanh::lean_dec_ref(v_inst_2518_);
        crate::leanh::lean_dec(v_inst_2517_);
        v_val_2524_ = crate::leanh::lean_ctor_get(v_natCastFn_x3f_2523_, 0);
        crate::leanh::lean_inc(v_val_2524_);
        crate::leanh::lean_dec_ref_known(v_natCastFn_x3f_2523_, 1);
        v___x_2525_ =
            crate::leanh::lean_apply_2(v_toPure_2516_, crate::leanh::lean_box(0), v_val_2524_);
        return v___x_2525_;
    } else {
        let mut v_type_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2516_);
        v_type_2526_ = crate::leanh::lean_ctor_get(v_ring_2522_, 1);
        crate::leanh::lean_inc_ref(v_type_2526_);
        v_u_2527_ = crate::leanh::lean_ctor_get(v_ring_2522_, 2);
        crate::leanh::lean_inc(v_u_2527_);
        v_semiringInst_2528_ = crate::leanh::lean_ctor_get(v_ring_2522_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_2528_);
        crate::leanh::lean_dec_ref(v_ring_2522_);
        v___x_2529_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(
                v_inst_2517_,
                v_inst_2518_,
                v_inst_2519_,
                v_u_2527_,
                v_type_2526_,
                v_semiringInst_2528_,
            );
        v___x_2530_ = crate::leanh::lean_apply_4(
            v_toBind_2520_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2529_,
            v___f_2521_,
        );
        return v___x_2530_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(
    mut v_inst_2531_: *mut crate::leanh::LeanObject,
    mut v_inst_2532_: *mut crate::leanh::LeanObject,
    mut v_inst_2533_: *mut crate::leanh::LeanObject,
    mut v_inst_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2535_ = crate::leanh::lean_ctor_get(v_inst_2532_, 0);
    v_toBind_2536_ = crate::leanh::lean_ctor_get(v_inst_2532_, 1);
    crate::leanh::lean_inc_n(v_toBind_2536_, 3);
    v_getRing_2537_ = crate::leanh::lean_ctor_get(v_inst_2534_, 0);
    crate::leanh::lean_inc(v_getRing_2537_);
    v_modifyRing_2538_ = crate::leanh::lean_ctor_get(v_inst_2534_, 1);
    crate::leanh::lean_inc(v_modifyRing_2538_);
    crate::leanh::lean_dec_ref(v_inst_2534_);
    v_toPure_2539_ = crate::leanh::lean_ctor_get(v_toApplicative_2535_, 1);
    crate::leanh::lean_inc_n(v_toPure_2539_, 2);
    v___f_2540_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2540_, 0, v_toPure_2539_);
    crate::leanh::lean_closure_set(v___f_2540_, 1, v_modifyRing_2538_);
    crate::leanh::lean_closure_set(v___f_2540_, 2, v_toBind_2536_);
    v___f_2541_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2541_, 0, v_toPure_2539_);
    crate::leanh::lean_closure_set(v___f_2541_, 1, v_inst_2531_);
    crate::leanh::lean_closure_set(v___f_2541_, 2, v_inst_2532_);
    crate::leanh::lean_closure_set(v___f_2541_, 3, v_inst_2533_);
    crate::leanh::lean_closure_set(v___f_2541_, 4, v_toBind_2536_);
    crate::leanh::lean_closure_set(v___f_2541_, 5, v___f_2540_);
    v___x_2542_ = crate::leanh::lean_apply_4(
        v_toBind_2536_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2537_,
        v___f_2541_,
    );
    return v___x_2542_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn(
    mut v_m_2543_: *mut crate::leanh::LeanObject,
    mut v_inst_2544_: *mut crate::leanh::LeanObject,
    mut v_inst_2545_: *mut crate::leanh::LeanObject,
    mut v_inst_2546_: *mut crate::leanh::LeanObject,
    mut v_inst_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2548_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(
        v_inst_2544_,
        v_inst_2545_,
        v_inst_2546_,
        v_inst_2547_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(
    mut v_invFn_2549_: *mut crate::leanh::LeanObject,
    mut v_s_2550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2551_ = crate::leanh::lean_ctor_get(v_s_2550_, 0);
                v_semiringId_x3f_2552_ = crate::leanh::lean_ctor_get(v_s_2550_, 2);
                v_commSemiringInst_2553_ = crate::leanh::lean_ctor_get(v_s_2550_, 3);
                v_commRingInst_2554_ = crate::leanh::lean_ctor_get(v_s_2550_, 4);
                v_noZeroDivInst_x3f_2555_ = crate::leanh::lean_ctor_get(v_s_2550_, 5);
                v_fieldInst_x3f_2556_ = crate::leanh::lean_ctor_get(v_s_2550_, 6);
                v_isSharedCheck_2564_ = (!crate::leanh::lean_is_exclusive(v_s_2550_)) as u8;
                if v_isSharedCheck_2564_ == 0 {
                    v_unused_2565_ = crate::leanh::lean_ctor_get(v_s_2550_, 1);
                    crate::leanh::lean_dec(v_unused_2565_);
                    v___x_2558_ = v_s_2550_;
                    v_isShared_2559_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fieldInst_x3f_2556_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2555_);
                    crate::leanh::lean_inc(v_commRingInst_2554_);
                    crate::leanh::lean_inc(v_commSemiringInst_2553_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2552_);
                    crate::leanh::lean_inc(v_toRing_2551_);
                    crate::leanh::lean_dec(v_s_2550_);
                    v___x_2558_ = crate::leanh::lean_box(0);
                    v_isShared_2559_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2560_, 0, v_invFn_2549_);
                if v_isShared_2559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2558_, 1, v___x_2560_);
                    v___x_2562_ = v___x_2558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2563_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_toRing_2551_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_semiringId_x3f_2552_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2563_,
                        3,
                        v_commSemiringInst_2553_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_commRingInst_2554_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2563_,
                        5,
                        v_noZeroDivInst_x3f_2555_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_fieldInst_x3f_2556_);
                    v___x_2562_ = v_reuseFailAlloc_2563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(
    mut v_toPure_2566_: *mut crate::leanh::LeanObject,
    mut v_invFn_2567_: *mut crate::leanh::LeanObject,
    mut v_____r_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2569_ =
        crate::leanh::lean_apply_2(v_toPure_2566_, crate::leanh::lean_box(0), v_invFn_2567_);
    return v___x_2569_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(
    mut v_toPure_2570_: *mut crate::leanh::LeanObject,
    mut v_modifyCommRing_2571_: *mut crate::leanh::LeanObject,
    mut v_toBind_2572_: *mut crate::leanh::LeanObject,
    mut v_invFn_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_invFn_2573_);
    v___f_2574_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2574_, 0, v_invFn_2573_);
    v___f_2575_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2575_, 0, v_toPure_2570_);
    crate::leanh::lean_closure_set(v___f_2575_, 1, v_invFn_2573_);
    v___x_2576_ = crate::leanh::lean_apply_1(v_modifyCommRing_2571_, v___f_2574_);
    v___x_2577_ = crate::leanh::lean_apply_4(
        v_toBind_2572_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2576_,
        v___f_2575_,
    );
    return v___x_2577_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7;
    v___x_2594_ = l_Lean_stringToMessageData(v___x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(
    mut v_toPure_2595_: *mut crate::leanh::LeanObject,
    mut v_inst_2596_: *mut crate::leanh::LeanObject,
    mut v_inst_2597_: *mut crate::leanh::LeanObject,
    mut v_inst_2598_: *mut crate::leanh::LeanObject,
    mut v_inst_2599_: *mut crate::leanh::LeanObject,
    mut v_toBind_2600_: *mut crate::leanh::LeanObject,
    mut v___f_2601_: *mut crate::leanh::LeanObject,
    mut v_ring_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fieldInst_x3f_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fieldInst_x3f_2603_ = crate::leanh::lean_ctor_get(v_ring_2602_, 6);
    if crate::leanh::lean_obj_tag(v_fieldInst_x3f_2603_) == 1 {
        let mut v_invFn_x3f_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_fieldInst_x3f_2603_);
        v_invFn_x3f_2604_ = crate::leanh::lean_ctor_get(v_ring_2602_, 1);
        if crate::leanh::lean_obj_tag(v_invFn_x3f_2604_) == 1 {
            let mut v_val_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_invFn_x3f_2604_);
            crate::leanh::lean_dec_ref_known(v_fieldInst_x3f_2603_, 1);
            crate::leanh::lean_dec_ref(v_ring_2602_);
            crate::leanh::lean_dec(v___f_2601_);
            crate::leanh::lean_dec(v_toBind_2600_);
            crate::leanh::lean_dec_ref(v_inst_2599_);
            crate::leanh::lean_dec_ref(v_inst_2598_);
            crate::leanh::lean_dec_ref(v_inst_2597_);
            crate::leanh::lean_dec(v_inst_2596_);
            v_val_2605_ = crate::leanh::lean_ctor_get(v_invFn_x3f_2604_, 0);
            crate::leanh::lean_inc(v_val_2605_);
            crate::leanh::lean_dec_ref_known(v_invFn_x3f_2604_, 1);
            v___x_2606_ =
                crate::leanh::lean_apply_2(v_toPure_2595_, crate::leanh::lean_box(0), v_val_2605_);
            return v___x_2606_;
        } else {
            let mut v_toRing_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_u_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedInst_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_2595_);
            v_toRing_2607_ = crate::leanh::lean_ctor_get(v_ring_2602_, 0);
            crate::leanh::lean_inc_ref(v_toRing_2607_);
            crate::leanh::lean_dec_ref(v_ring_2602_);
            v_val_2608_ = crate::leanh::lean_ctor_get(v_fieldInst_x3f_2603_, 0);
            crate::leanh::lean_inc(v_val_2608_);
            crate::leanh::lean_dec_ref_known(v_fieldInst_x3f_2603_, 1);
            v_type_2609_ = crate::leanh::lean_ctor_get(v_toRing_2607_, 1);
            crate::leanh::lean_inc_ref_n(v_type_2609_, 2);
            v_u_2610_ = crate::leanh::lean_ctor_get(v_toRing_2607_, 2);
            crate::leanh::lean_inc_n(v_u_2610_, 2);
            crate::leanh::lean_dec_ref(v_toRing_2607_);
            v___x_2611_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2;
            v___x_2612_ = crate::leanh::lean_box(0);
            v___x_2613_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2613_, 0, v_u_2610_);
            crate::leanh::lean_ctor_set(v___x_2613_, 1, v___x_2612_);
            v___x_2614_ = l_Lean_mkConst(v___x_2611_, v___x_2613_);
            v_expectedInst_2615_ = l_Lean_mkAppB(v___x_2614_, v_type_2609_, v_val_2608_);
            v___x_2616_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4;
            v___x_2617_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6;
            v___x_2618_ =
                l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(
                    v_inst_2596_,
                    v_inst_2597_,
                    v_inst_2598_,
                    v_inst_2599_,
                    v_type_2609_,
                    v_u_2610_,
                    v___x_2616_,
                    v___x_2617_,
                    v_expectedInst_2615_,
                );
            v___x_2619_ = crate::leanh::lean_apply_4(
                v_toBind_2600_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2618_,
                v___f_2601_,
            );
            return v___x_2619_;
        }
    } else {
        let mut v_toRing_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2601_);
        crate::leanh::lean_dec(v_toBind_2600_);
        crate::leanh::lean_dec_ref(v_inst_2599_);
        crate::leanh::lean_dec(v_inst_2596_);
        crate::leanh::lean_dec(v_toPure_2595_);
        v_toRing_2620_ = crate::leanh::lean_ctor_get(v_ring_2602_, 0);
        crate::leanh::lean_inc_ref(v_toRing_2620_);
        crate::leanh::lean_dec_ref(v_ring_2602_);
        v_type_2621_ = crate::leanh::lean_ctor_get(v_toRing_2620_, 1);
        crate::leanh::lean_inc_ref(v_type_2621_);
        crate::leanh::lean_dec_ref(v_toRing_2620_);
        v___x_2622_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once
            ),
            _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8,
        );
        v___x_2623_ = l_Lean_indentExpr(v_type_2621_);
        v___x_2624_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2624_, 0, v___x_2622_);
        crate::leanh::lean_ctor_set(v___x_2624_, 1, v___x_2623_);
        v___x_2625_ = l_Lean_throwError___redArg(v_inst_2598_, v_inst_2597_, v___x_2624_);
        return v___x_2625_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg(
    mut v_inst_2626_: *mut crate::leanh::LeanObject,
    mut v_inst_2627_: *mut crate::leanh::LeanObject,
    mut v_inst_2628_: *mut crate::leanh::LeanObject,
    mut v_inst_2629_: *mut crate::leanh::LeanObject,
    mut v_inst_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2631_ = crate::leanh::lean_ctor_get(v_inst_2628_, 0);
    v_toBind_2632_ = crate::leanh::lean_ctor_get(v_inst_2628_, 1);
    crate::leanh::lean_inc_n(v_toBind_2632_, 3);
    v_getCommRing_2633_ = crate::leanh::lean_ctor_get(v_inst_2630_, 0);
    crate::leanh::lean_inc(v_getCommRing_2633_);
    v_modifyCommRing_2634_ = crate::leanh::lean_ctor_get(v_inst_2630_, 1);
    crate::leanh::lean_inc(v_modifyCommRing_2634_);
    crate::leanh::lean_dec_ref(v_inst_2630_);
    v_toPure_2635_ = crate::leanh::lean_ctor_get(v_toApplicative_2631_, 1);
    crate::leanh::lean_inc_n(v_toPure_2635_, 2);
    v___f_2636_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2636_, 0, v_toPure_2635_);
    crate::leanh::lean_closure_set(v___f_2636_, 1, v_modifyCommRing_2634_);
    crate::leanh::lean_closure_set(v___f_2636_, 2, v_toBind_2632_);
    v___f_2637_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2637_, 0, v_toPure_2635_);
    crate::leanh::lean_closure_set(v___f_2637_, 1, v_inst_2626_);
    crate::leanh::lean_closure_set(v___f_2637_, 2, v_inst_2627_);
    crate::leanh::lean_closure_set(v___f_2637_, 3, v_inst_2628_);
    crate::leanh::lean_closure_set(v___f_2637_, 4, v_inst_2629_);
    crate::leanh::lean_closure_set(v___f_2637_, 5, v_toBind_2632_);
    crate::leanh::lean_closure_set(v___f_2637_, 6, v___f_2636_);
    v___x_2638_ = crate::leanh::lean_apply_4(
        v_toBind_2632_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCommRing_2633_,
        v___f_2637_,
    );
    return v___x_2638_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn(
    mut v_m_2639_: *mut crate::leanh::LeanObject,
    mut v_inst_2640_: *mut crate::leanh::LeanObject,
    mut v_inst_2641_: *mut crate::leanh::LeanObject,
    mut v_inst_2642_: *mut crate::leanh::LeanObject,
    mut v_inst_2643_: *mut crate::leanh::LeanObject,
    mut v_inst_2644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(
        v_inst_2640_,
        v_inst_2641_,
        v_inst_2642_,
        v_inst_2643_,
        v_inst_2644_,
    );
    return v___x_2645_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(
    mut v_addFn_2646_: *mut crate::leanh::LeanObject,
    mut v_s_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_unused_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2648_ = crate::leanh::lean_ctor_get(v_s_2647_, 0);
                v_type_2649_ = crate::leanh::lean_ctor_get(v_s_2647_, 1);
                v_u_2650_ = crate::leanh::lean_ctor_get(v_s_2647_, 2);
                v_semiringInst_2651_ = crate::leanh::lean_ctor_get(v_s_2647_, 3);
                v_mulFn_x3f_2652_ = crate::leanh::lean_ctor_get(v_s_2647_, 5);
                v_powFn_x3f_2653_ = crate::leanh::lean_ctor_get(v_s_2647_, 6);
                v_natCastFn_x3f_2654_ = crate::leanh::lean_ctor_get(v_s_2647_, 7);
                v_isSharedCheck_2662_ = (!crate::leanh::lean_is_exclusive(v_s_2647_)) as u8;
                if v_isSharedCheck_2662_ == 0 {
                    v_unused_2663_ = crate::leanh::lean_ctor_get(v_s_2647_, 4);
                    crate::leanh::lean_dec(v_unused_2663_);
                    v___x_2656_ = v_s_2647_;
                    v_isShared_2657_ = v_isSharedCheck_2662_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_natCastFn_x3f_2654_);
                    crate::leanh::lean_inc(v_powFn_x3f_2653_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2652_);
                    crate::leanh::lean_inc(v_semiringInst_2651_);
                    crate::leanh::lean_inc(v_u_2650_);
                    crate::leanh::lean_inc(v_type_2649_);
                    crate::leanh::lean_inc(v_id_2648_);
                    crate::leanh::lean_dec(v_s_2647_);
                    v___x_2656_ = crate::leanh::lean_box(0);
                    v_isShared_2657_ = v_isSharedCheck_2662_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2658_, 0, v_addFn_2646_);
                if v_isShared_2657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2656_, 4, v___x_2658_);
                    v___x_2660_ = v___x_2656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_id_2648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_type_2649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_u_2650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 3, v_semiringInst_2651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 4, v___x_2658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 5, v_mulFn_x3f_2652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 6, v_powFn_x3f_2653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 7, v_natCastFn_x3f_2654_);
                    v___x_2660_ = v_reuseFailAlloc_2661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(
    mut v_toPure_2664_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_2665_: *mut crate::leanh::LeanObject,
    mut v_toBind_2666_: *mut crate::leanh::LeanObject,
    mut v_addFn_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_addFn_2667_);
    v___f_2668_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2668_, 0, v_addFn_2667_);
    v___f_2669_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2669_, 0, v_toPure_2664_);
    crate::leanh::lean_closure_set(v___f_2669_, 1, v_addFn_2667_);
    v___x_2670_ = crate::leanh::lean_apply_1(v_modifySemiring_2665_, v___f_2668_);
    v___x_2671_ = crate::leanh::lean_apply_4(
        v_toBind_2666_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2670_,
        v___f_2669_,
    );
    return v___x_2671_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(
    mut v_toPure_2672_: *mut crate::leanh::LeanObject,
    mut v_inst_2673_: *mut crate::leanh::LeanObject,
    mut v_inst_2674_: *mut crate::leanh::LeanObject,
    mut v_inst_2675_: *mut crate::leanh::LeanObject,
    mut v_inst_2676_: *mut crate::leanh::LeanObject,
    mut v_toBind_2677_: *mut crate::leanh::LeanObject,
    mut v___f_2678_: *mut crate::leanh::LeanObject,
    mut v_sr_2679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_addFn_x3f_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_addFn_x3f_2680_ = crate::leanh::lean_ctor_get(v_sr_2679_, 4);
    if crate::leanh::lean_obj_tag(v_addFn_x3f_2680_) == 1 {
        let mut v_val_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_addFn_x3f_2680_);
        crate::leanh::lean_dec_ref(v_sr_2679_);
        crate::leanh::lean_dec(v___f_2678_);
        crate::leanh::lean_dec(v_toBind_2677_);
        crate::leanh::lean_dec_ref(v_inst_2676_);
        crate::leanh::lean_dec_ref(v_inst_2675_);
        crate::leanh::lean_dec_ref(v_inst_2674_);
        crate::leanh::lean_dec(v_inst_2673_);
        v_val_2681_ = crate::leanh::lean_ctor_get(v_addFn_x3f_2680_, 0);
        crate::leanh::lean_inc(v_val_2681_);
        crate::leanh::lean_dec_ref_known(v_addFn_x3f_2680_, 1);
        v___x_2682_ =
            crate::leanh::lean_apply_2(v_toPure_2672_, crate::leanh::lean_box(0), v_val_2681_);
        return v___x_2682_;
    } else {
        let mut v_type_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2672_);
        v_type_2683_ = crate::leanh::lean_ctor_get(v_sr_2679_, 1);
        crate::leanh::lean_inc_ref_n(v_type_2683_, 3);
        v_u_2684_ = crate::leanh::lean_ctor_get(v_sr_2679_, 2);
        crate::leanh::lean_inc_n(v_u_2684_, 2);
        v_semiringInst_2685_ = crate::leanh::lean_ctor_get(v_sr_2679_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_2685_);
        crate::leanh::lean_dec_ref(v_sr_2679_);
        v___x_2686_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1;
        v___x_2687_ = crate::leanh::lean_box(0);
        v___x_2688_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2688_, 0, v_u_2684_);
        crate::leanh::lean_ctor_set(v___x_2688_, 1, v___x_2687_);
        crate::leanh::lean_inc_ref(v___x_2688_);
        v___x_2689_ = l_Lean_mkConst(v___x_2686_, v___x_2688_);
        v___x_2690_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3;
        v___x_2691_ = l_Lean_mkConst(v___x_2690_, v___x_2688_);
        v___x_2692_ = l_Lean_mkAppB(v___x_2691_, v_type_2683_, v_semiringInst_2685_);
        v_expectedInst_2693_ = l_Lean_mkAppB(v___x_2689_, v_type_2683_, v___x_2692_);
        v___x_2694_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5;
        v___x_2695_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7;
        v___x_2696_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
                v_inst_2673_,
                v_inst_2674_,
                v_inst_2675_,
                v_inst_2676_,
                v_type_2683_,
                v_u_2684_,
                v___x_2694_,
                v___x_2695_,
                v_expectedInst_2693_,
            );
        v___x_2697_ = crate::leanh::lean_apply_4(
            v_toBind_2677_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2696_,
            v___f_2678_,
        );
        return v___x_2697_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(
    mut v_inst_2698_: *mut crate::leanh::LeanObject,
    mut v_inst_2699_: *mut crate::leanh::LeanObject,
    mut v_inst_2700_: *mut crate::leanh::LeanObject,
    mut v_inst_2701_: *mut crate::leanh::LeanObject,
    mut v_inst_2702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2703_ = crate::leanh::lean_ctor_get(v_inst_2700_, 0);
    v_toBind_2704_ = crate::leanh::lean_ctor_get(v_inst_2700_, 1);
    crate::leanh::lean_inc_n(v_toBind_2704_, 3);
    v_getSemiring_2705_ = crate::leanh::lean_ctor_get(v_inst_2702_, 0);
    crate::leanh::lean_inc(v_getSemiring_2705_);
    v_modifySemiring_2706_ = crate::leanh::lean_ctor_get(v_inst_2702_, 1);
    crate::leanh::lean_inc(v_modifySemiring_2706_);
    crate::leanh::lean_dec_ref(v_inst_2702_);
    v_toPure_2707_ = crate::leanh::lean_ctor_get(v_toApplicative_2703_, 1);
    crate::leanh::lean_inc_n(v_toPure_2707_, 2);
    v___f_2708_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2708_, 0, v_toPure_2707_);
    crate::leanh::lean_closure_set(v___f_2708_, 1, v_modifySemiring_2706_);
    crate::leanh::lean_closure_set(v___f_2708_, 2, v_toBind_2704_);
    v___f_2709_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2709_, 0, v_toPure_2707_);
    crate::leanh::lean_closure_set(v___f_2709_, 1, v_inst_2698_);
    crate::leanh::lean_closure_set(v___f_2709_, 2, v_inst_2699_);
    crate::leanh::lean_closure_set(v___f_2709_, 3, v_inst_2700_);
    crate::leanh::lean_closure_set(v___f_2709_, 4, v_inst_2701_);
    crate::leanh::lean_closure_set(v___f_2709_, 5, v_toBind_2704_);
    crate::leanh::lean_closure_set(v___f_2709_, 6, v___f_2708_);
    v___x_2710_ = crate::leanh::lean_apply_4(
        v_toBind_2704_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_2705_,
        v___f_2709_,
    );
    return v___x_2710_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27(
    mut v_m_2711_: *mut crate::leanh::LeanObject,
    mut v_inst_2712_: *mut crate::leanh::LeanObject,
    mut v_inst_2713_: *mut crate::leanh::LeanObject,
    mut v_inst_2714_: *mut crate::leanh::LeanObject,
    mut v_inst_2715_: *mut crate::leanh::LeanObject,
    mut v_inst_2716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2717_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(
        v_inst_2712_,
        v_inst_2713_,
        v_inst_2714_,
        v_inst_2715_,
        v_inst_2716_,
    );
    return v___x_2717_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(
    mut v_mulFn_2718_: *mut crate::leanh::LeanObject,
    mut v_s_2719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_unused_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2720_ = crate::leanh::lean_ctor_get(v_s_2719_, 0);
                v_type_2721_ = crate::leanh::lean_ctor_get(v_s_2719_, 1);
                v_u_2722_ = crate::leanh::lean_ctor_get(v_s_2719_, 2);
                v_semiringInst_2723_ = crate::leanh::lean_ctor_get(v_s_2719_, 3);
                v_addFn_x3f_2724_ = crate::leanh::lean_ctor_get(v_s_2719_, 4);
                v_powFn_x3f_2725_ = crate::leanh::lean_ctor_get(v_s_2719_, 6);
                v_natCastFn_x3f_2726_ = crate::leanh::lean_ctor_get(v_s_2719_, 7);
                v_isSharedCheck_2734_ = (!crate::leanh::lean_is_exclusive(v_s_2719_)) as u8;
                if v_isSharedCheck_2734_ == 0 {
                    v_unused_2735_ = crate::leanh::lean_ctor_get(v_s_2719_, 5);
                    crate::leanh::lean_dec(v_unused_2735_);
                    v___x_2728_ = v_s_2719_;
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_natCastFn_x3f_2726_);
                    crate::leanh::lean_inc(v_powFn_x3f_2725_);
                    crate::leanh::lean_inc(v_addFn_x3f_2724_);
                    crate::leanh::lean_inc(v_semiringInst_2723_);
                    crate::leanh::lean_inc(v_u_2722_);
                    crate::leanh::lean_inc(v_type_2721_);
                    crate::leanh::lean_inc(v_id_2720_);
                    crate::leanh::lean_dec(v_s_2719_);
                    v___x_2728_ = crate::leanh::lean_box(0);
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2730_, 0, v_mulFn_2718_);
                if v_isShared_2729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2728_, 5, v___x_2730_);
                    v___x_2732_ = v___x_2728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_id_2720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_type_2721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_u_2722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_semiringInst_2723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_addFn_x3f_2724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 5, v___x_2730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 6, v_powFn_x3f_2725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 7, v_natCastFn_x3f_2726_);
                    v___x_2732_ = v_reuseFailAlloc_2733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(
    mut v_toPure_2736_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_2737_: *mut crate::leanh::LeanObject,
    mut v_toBind_2738_: *mut crate::leanh::LeanObject,
    mut v_mulFn_2739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_mulFn_2739_);
    v___f_2740_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2740_, 0, v_mulFn_2739_);
    v___f_2741_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2741_, 0, v_toPure_2736_);
    crate::leanh::lean_closure_set(v___f_2741_, 1, v_mulFn_2739_);
    v___x_2742_ = crate::leanh::lean_apply_1(v_modifySemiring_2737_, v___f_2740_);
    v___x_2743_ = crate::leanh::lean_apply_4(
        v_toBind_2738_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2742_,
        v___f_2741_,
    );
    return v___x_2743_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(
    mut v_toPure_2744_: *mut crate::leanh::LeanObject,
    mut v_inst_2745_: *mut crate::leanh::LeanObject,
    mut v_inst_2746_: *mut crate::leanh::LeanObject,
    mut v_inst_2747_: *mut crate::leanh::LeanObject,
    mut v_inst_2748_: *mut crate::leanh::LeanObject,
    mut v_toBind_2749_: *mut crate::leanh::LeanObject,
    mut v___f_2750_: *mut crate::leanh::LeanObject,
    mut v_sr_2751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mulFn_x3f_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_2752_ = crate::leanh::lean_ctor_get(v_sr_2751_, 5);
    if crate::leanh::lean_obj_tag(v_mulFn_x3f_2752_) == 1 {
        let mut v_val_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_mulFn_x3f_2752_);
        crate::leanh::lean_dec_ref(v_sr_2751_);
        crate::leanh::lean_dec(v___f_2750_);
        crate::leanh::lean_dec(v_toBind_2749_);
        crate::leanh::lean_dec_ref(v_inst_2748_);
        crate::leanh::lean_dec_ref(v_inst_2747_);
        crate::leanh::lean_dec_ref(v_inst_2746_);
        crate::leanh::lean_dec(v_inst_2745_);
        v_val_2753_ = crate::leanh::lean_ctor_get(v_mulFn_x3f_2752_, 0);
        crate::leanh::lean_inc(v_val_2753_);
        crate::leanh::lean_dec_ref_known(v_mulFn_x3f_2752_, 1);
        v___x_2754_ =
            crate::leanh::lean_apply_2(v_toPure_2744_, crate::leanh::lean_box(0), v_val_2753_);
        return v___x_2754_;
    } else {
        let mut v_type_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2744_);
        v_type_2755_ = crate::leanh::lean_ctor_get(v_sr_2751_, 1);
        crate::leanh::lean_inc_ref_n(v_type_2755_, 3);
        v_u_2756_ = crate::leanh::lean_ctor_get(v_sr_2751_, 2);
        crate::leanh::lean_inc_n(v_u_2756_, 2);
        v_semiringInst_2757_ = crate::leanh::lean_ctor_get(v_sr_2751_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_2757_);
        crate::leanh::lean_dec_ref(v_sr_2751_);
        v___x_2758_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1;
        v___x_2759_ = crate::leanh::lean_box(0);
        v___x_2760_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2760_, 0, v_u_2756_);
        crate::leanh::lean_ctor_set(v___x_2760_, 1, v___x_2759_);
        crate::leanh::lean_inc_ref(v___x_2760_);
        v___x_2761_ = l_Lean_mkConst(v___x_2758_, v___x_2760_);
        v___x_2762_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3;
        v___x_2763_ = l_Lean_mkConst(v___x_2762_, v___x_2760_);
        v___x_2764_ = l_Lean_mkAppB(v___x_2763_, v_type_2755_, v_semiringInst_2757_);
        v_expectedInst_2765_ = l_Lean_mkAppB(v___x_2761_, v_type_2755_, v___x_2764_);
        v___x_2766_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5;
        v___x_2767_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7;
        v___x_2768_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
                v_inst_2745_,
                v_inst_2746_,
                v_inst_2747_,
                v_inst_2748_,
                v_type_2755_,
                v_u_2756_,
                v___x_2766_,
                v___x_2767_,
                v_expectedInst_2765_,
            );
        v___x_2769_ = crate::leanh::lean_apply_4(
            v_toBind_2749_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2768_,
            v___f_2750_,
        );
        return v___x_2769_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(
    mut v_inst_2770_: *mut crate::leanh::LeanObject,
    mut v_inst_2771_: *mut crate::leanh::LeanObject,
    mut v_inst_2772_: *mut crate::leanh::LeanObject,
    mut v_inst_2773_: *mut crate::leanh::LeanObject,
    mut v_inst_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2775_ = crate::leanh::lean_ctor_get(v_inst_2772_, 0);
    v_toBind_2776_ = crate::leanh::lean_ctor_get(v_inst_2772_, 1);
    crate::leanh::lean_inc_n(v_toBind_2776_, 3);
    v_getSemiring_2777_ = crate::leanh::lean_ctor_get(v_inst_2774_, 0);
    crate::leanh::lean_inc(v_getSemiring_2777_);
    v_modifySemiring_2778_ = crate::leanh::lean_ctor_get(v_inst_2774_, 1);
    crate::leanh::lean_inc(v_modifySemiring_2778_);
    crate::leanh::lean_dec_ref(v_inst_2774_);
    v_toPure_2779_ = crate::leanh::lean_ctor_get(v_toApplicative_2775_, 1);
    crate::leanh::lean_inc_n(v_toPure_2779_, 2);
    v___f_2780_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2780_, 0, v_toPure_2779_);
    crate::leanh::lean_closure_set(v___f_2780_, 1, v_modifySemiring_2778_);
    crate::leanh::lean_closure_set(v___f_2780_, 2, v_toBind_2776_);
    v___f_2781_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2781_, 0, v_toPure_2779_);
    crate::leanh::lean_closure_set(v___f_2781_, 1, v_inst_2770_);
    crate::leanh::lean_closure_set(v___f_2781_, 2, v_inst_2771_);
    crate::leanh::lean_closure_set(v___f_2781_, 3, v_inst_2772_);
    crate::leanh::lean_closure_set(v___f_2781_, 4, v_inst_2773_);
    crate::leanh::lean_closure_set(v___f_2781_, 5, v_toBind_2776_);
    crate::leanh::lean_closure_set(v___f_2781_, 6, v___f_2780_);
    v___x_2782_ = crate::leanh::lean_apply_4(
        v_toBind_2776_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_2777_,
        v___f_2781_,
    );
    return v___x_2782_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27(
    mut v_m_2783_: *mut crate::leanh::LeanObject,
    mut v_inst_2784_: *mut crate::leanh::LeanObject,
    mut v_inst_2785_: *mut crate::leanh::LeanObject,
    mut v_inst_2786_: *mut crate::leanh::LeanObject,
    mut v_inst_2787_: *mut crate::leanh::LeanObject,
    mut v_inst_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2789_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(
        v_inst_2784_,
        v_inst_2785_,
        v_inst_2786_,
        v_inst_2787_,
        v_inst_2788_,
    );
    return v___x_2789_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(
    mut v_powFn_2790_: *mut crate::leanh::LeanObject,
    mut v_s_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_unused_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2792_ = crate::leanh::lean_ctor_get(v_s_2791_, 0);
                v_type_2793_ = crate::leanh::lean_ctor_get(v_s_2791_, 1);
                v_u_2794_ = crate::leanh::lean_ctor_get(v_s_2791_, 2);
                v_semiringInst_2795_ = crate::leanh::lean_ctor_get(v_s_2791_, 3);
                v_addFn_x3f_2796_ = crate::leanh::lean_ctor_get(v_s_2791_, 4);
                v_mulFn_x3f_2797_ = crate::leanh::lean_ctor_get(v_s_2791_, 5);
                v_natCastFn_x3f_2798_ = crate::leanh::lean_ctor_get(v_s_2791_, 7);
                v_isSharedCheck_2806_ = (!crate::leanh::lean_is_exclusive(v_s_2791_)) as u8;
                if v_isSharedCheck_2806_ == 0 {
                    v_unused_2807_ = crate::leanh::lean_ctor_get(v_s_2791_, 6);
                    crate::leanh::lean_dec(v_unused_2807_);
                    v___x_2800_ = v_s_2791_;
                    v_isShared_2801_ = v_isSharedCheck_2806_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_natCastFn_x3f_2798_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2797_);
                    crate::leanh::lean_inc(v_addFn_x3f_2796_);
                    crate::leanh::lean_inc(v_semiringInst_2795_);
                    crate::leanh::lean_inc(v_u_2794_);
                    crate::leanh::lean_inc(v_type_2793_);
                    crate::leanh::lean_inc(v_id_2792_);
                    crate::leanh::lean_dec(v_s_2791_);
                    v___x_2800_ = crate::leanh::lean_box(0);
                    v_isShared_2801_ = v_isSharedCheck_2806_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2802_, 0, v_powFn_2790_);
                if v_isShared_2801_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2800_, 6, v___x_2802_);
                    v___x_2804_ = v___x_2800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_id_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_type_2793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_u_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_semiringInst_2795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_addFn_x3f_2796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 5, v_mulFn_x3f_2797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 6, v___x_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 7, v_natCastFn_x3f_2798_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(
    mut v_toPure_2808_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_2809_: *mut crate::leanh::LeanObject,
    mut v_toBind_2810_: *mut crate::leanh::LeanObject,
    mut v_powFn_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_powFn_2811_);
    v___f_2812_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2812_, 0, v_powFn_2811_);
    v___f_2813_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2813_, 0, v_toPure_2808_);
    crate::leanh::lean_closure_set(v___f_2813_, 1, v_powFn_2811_);
    v___x_2814_ = crate::leanh::lean_apply_1(v_modifySemiring_2809_, v___f_2812_);
    v___x_2815_ = crate::leanh::lean_apply_4(
        v_toBind_2810_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2814_,
        v___f_2813_,
    );
    return v___x_2815_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(
    mut v_toPure_2816_: *mut crate::leanh::LeanObject,
    mut v_inst_2817_: *mut crate::leanh::LeanObject,
    mut v_inst_2818_: *mut crate::leanh::LeanObject,
    mut v_inst_2819_: *mut crate::leanh::LeanObject,
    mut v_inst_2820_: *mut crate::leanh::LeanObject,
    mut v_toBind_2821_: *mut crate::leanh::LeanObject,
    mut v___f_2822_: *mut crate::leanh::LeanObject,
    mut v_sr_2823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_powFn_x3f_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_powFn_x3f_2824_ = crate::leanh::lean_ctor_get(v_sr_2823_, 6);
    if crate::leanh::lean_obj_tag(v_powFn_x3f_2824_) == 1 {
        let mut v_val_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_powFn_x3f_2824_);
        crate::leanh::lean_dec_ref(v_sr_2823_);
        crate::leanh::lean_dec(v___f_2822_);
        crate::leanh::lean_dec(v_toBind_2821_);
        crate::leanh::lean_dec_ref(v_inst_2820_);
        crate::leanh::lean_dec_ref(v_inst_2819_);
        crate::leanh::lean_dec_ref(v_inst_2818_);
        crate::leanh::lean_dec(v_inst_2817_);
        v_val_2825_ = crate::leanh::lean_ctor_get(v_powFn_x3f_2824_, 0);
        crate::leanh::lean_inc(v_val_2825_);
        crate::leanh::lean_dec_ref_known(v_powFn_x3f_2824_, 1);
        v___x_2826_ =
            crate::leanh::lean_apply_2(v_toPure_2816_, crate::leanh::lean_box(0), v_val_2825_);
        return v___x_2826_;
    } else {
        let mut v_type_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2816_);
        v_type_2827_ = crate::leanh::lean_ctor_get(v_sr_2823_, 1);
        crate::leanh::lean_inc_ref(v_type_2827_);
        v_u_2828_ = crate::leanh::lean_ctor_get(v_sr_2823_, 2);
        crate::leanh::lean_inc(v_u_2828_);
        v_semiringInst_2829_ = crate::leanh::lean_ctor_get(v_sr_2823_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_2829_);
        crate::leanh::lean_dec_ref(v_sr_2823_);
        v___x_2830_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(
                v_inst_2817_,
                v_inst_2818_,
                v_inst_2819_,
                v_inst_2820_,
                v_u_2828_,
                v_type_2827_,
                v_semiringInst_2829_,
            );
        v___x_2831_ = crate::leanh::lean_apply_4(
            v_toBind_2821_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2830_,
            v___f_2822_,
        );
        return v___x_2831_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(
    mut v_inst_2832_: *mut crate::leanh::LeanObject,
    mut v_inst_2833_: *mut crate::leanh::LeanObject,
    mut v_inst_2834_: *mut crate::leanh::LeanObject,
    mut v_inst_2835_: *mut crate::leanh::LeanObject,
    mut v_inst_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2837_ = crate::leanh::lean_ctor_get(v_inst_2834_, 0);
    v_toBind_2838_ = crate::leanh::lean_ctor_get(v_inst_2834_, 1);
    crate::leanh::lean_inc_n(v_toBind_2838_, 3);
    v_getSemiring_2839_ = crate::leanh::lean_ctor_get(v_inst_2836_, 0);
    crate::leanh::lean_inc(v_getSemiring_2839_);
    v_modifySemiring_2840_ = crate::leanh::lean_ctor_get(v_inst_2836_, 1);
    crate::leanh::lean_inc(v_modifySemiring_2840_);
    crate::leanh::lean_dec_ref(v_inst_2836_);
    v_toPure_2841_ = crate::leanh::lean_ctor_get(v_toApplicative_2837_, 1);
    crate::leanh::lean_inc_n(v_toPure_2841_, 2);
    v___f_2842_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2842_, 0, v_toPure_2841_);
    crate::leanh::lean_closure_set(v___f_2842_, 1, v_modifySemiring_2840_);
    crate::leanh::lean_closure_set(v___f_2842_, 2, v_toBind_2838_);
    v___f_2843_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2843_, 0, v_toPure_2841_);
    crate::leanh::lean_closure_set(v___f_2843_, 1, v_inst_2832_);
    crate::leanh::lean_closure_set(v___f_2843_, 2, v_inst_2833_);
    crate::leanh::lean_closure_set(v___f_2843_, 3, v_inst_2834_);
    crate::leanh::lean_closure_set(v___f_2843_, 4, v_inst_2835_);
    crate::leanh::lean_closure_set(v___f_2843_, 5, v_toBind_2838_);
    crate::leanh::lean_closure_set(v___f_2843_, 6, v___f_2842_);
    v___x_2844_ = crate::leanh::lean_apply_4(
        v_toBind_2838_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_2839_,
        v___f_2843_,
    );
    return v___x_2844_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27(
    mut v_m_2845_: *mut crate::leanh::LeanObject,
    mut v_inst_2846_: *mut crate::leanh::LeanObject,
    mut v_inst_2847_: *mut crate::leanh::LeanObject,
    mut v_inst_2848_: *mut crate::leanh::LeanObject,
    mut v_inst_2849_: *mut crate::leanh::LeanObject,
    mut v_inst_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2851_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(
        v_inst_2846_,
        v_inst_2847_,
        v_inst_2848_,
        v_inst_2849_,
        v_inst_2850_,
    );
    return v___x_2851_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(
    mut v_natCastFn_2852_: *mut crate::leanh::LeanObject,
    mut v_s_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_unused_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2854_ = crate::leanh::lean_ctor_get(v_s_2853_, 0);
                v_type_2855_ = crate::leanh::lean_ctor_get(v_s_2853_, 1);
                v_u_2856_ = crate::leanh::lean_ctor_get(v_s_2853_, 2);
                v_semiringInst_2857_ = crate::leanh::lean_ctor_get(v_s_2853_, 3);
                v_addFn_x3f_2858_ = crate::leanh::lean_ctor_get(v_s_2853_, 4);
                v_mulFn_x3f_2859_ = crate::leanh::lean_ctor_get(v_s_2853_, 5);
                v_powFn_x3f_2860_ = crate::leanh::lean_ctor_get(v_s_2853_, 6);
                v_isSharedCheck_2868_ = (!crate::leanh::lean_is_exclusive(v_s_2853_)) as u8;
                if v_isSharedCheck_2868_ == 0 {
                    v_unused_2869_ = crate::leanh::lean_ctor_get(v_s_2853_, 7);
                    crate::leanh::lean_dec(v_unused_2869_);
                    v___x_2862_ = v_s_2853_;
                    v_isShared_2863_ = v_isSharedCheck_2868_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_powFn_x3f_2860_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2859_);
                    crate::leanh::lean_inc(v_addFn_x3f_2858_);
                    crate::leanh::lean_inc(v_semiringInst_2857_);
                    crate::leanh::lean_inc(v_u_2856_);
                    crate::leanh::lean_inc(v_type_2855_);
                    crate::leanh::lean_inc(v_id_2854_);
                    crate::leanh::lean_dec(v_s_2853_);
                    v___x_2862_ = crate::leanh::lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2868_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2864_, 0, v_natCastFn_2852_);
                if v_isShared_2863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2862_, 7, v___x_2864_);
                    v___x_2866_ = v___x_2862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_id_2854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_type_2855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_u_2856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 3, v_semiringInst_2857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 4, v_addFn_x3f_2858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 5, v_mulFn_x3f_2859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 6, v_powFn_x3f_2860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 7, v___x_2864_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(
    mut v_toPure_2870_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_2871_: *mut crate::leanh::LeanObject,
    mut v_toBind_2872_: *mut crate::leanh::LeanObject,
    mut v_natCastFn_2873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_natCastFn_2873_);
    v___f_2874_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2874_, 0, v_natCastFn_2873_);
    v___f_2875_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2875_, 0, v_toPure_2870_);
    crate::leanh::lean_closure_set(v___f_2875_, 1, v_natCastFn_2873_);
    v___x_2876_ = crate::leanh::lean_apply_1(v_modifySemiring_2871_, v___f_2874_);
    v___x_2877_ = crate::leanh::lean_apply_4(
        v_toBind_2872_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2876_,
        v___f_2875_,
    );
    return v___x_2877_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(
    mut v_toPure_2878_: *mut crate::leanh::LeanObject,
    mut v_inst_2879_: *mut crate::leanh::LeanObject,
    mut v_inst_2880_: *mut crate::leanh::LeanObject,
    mut v_inst_2881_: *mut crate::leanh::LeanObject,
    mut v_toBind_2882_: *mut crate::leanh::LeanObject,
    mut v___f_2883_: *mut crate::leanh::LeanObject,
    mut v_sr_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natCastFn_x3f_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_2885_ = crate::leanh::lean_ctor_get(v_sr_2884_, 7);
    if crate::leanh::lean_obj_tag(v_natCastFn_x3f_2885_) == 1 {
        let mut v_val_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_natCastFn_x3f_2885_);
        crate::leanh::lean_dec_ref(v_sr_2884_);
        crate::leanh::lean_dec(v___f_2883_);
        crate::leanh::lean_dec(v_toBind_2882_);
        crate::leanh::lean_dec_ref(v_inst_2881_);
        crate::leanh::lean_dec_ref(v_inst_2880_);
        crate::leanh::lean_dec(v_inst_2879_);
        v_val_2886_ = crate::leanh::lean_ctor_get(v_natCastFn_x3f_2885_, 0);
        crate::leanh::lean_inc(v_val_2886_);
        crate::leanh::lean_dec_ref_known(v_natCastFn_x3f_2885_, 1);
        v___x_2887_ =
            crate::leanh::lean_apply_2(v_toPure_2878_, crate::leanh::lean_box(0), v_val_2886_);
        return v___x_2887_;
    } else {
        let mut v_type_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2878_);
        v_type_2888_ = crate::leanh::lean_ctor_get(v_sr_2884_, 1);
        crate::leanh::lean_inc_ref(v_type_2888_);
        v_u_2889_ = crate::leanh::lean_ctor_get(v_sr_2884_, 2);
        crate::leanh::lean_inc(v_u_2889_);
        v_semiringInst_2890_ = crate::leanh::lean_ctor_get(v_sr_2884_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_2890_);
        crate::leanh::lean_dec_ref(v_sr_2884_);
        v___x_2891_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(
                v_inst_2879_,
                v_inst_2880_,
                v_inst_2881_,
                v_u_2889_,
                v_type_2888_,
                v_semiringInst_2890_,
            );
        v___x_2892_ = crate::leanh::lean_apply_4(
            v_toBind_2882_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2891_,
            v___f_2883_,
        );
        return v___x_2892_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(
    mut v_inst_2893_: *mut crate::leanh::LeanObject,
    mut v_inst_2894_: *mut crate::leanh::LeanObject,
    mut v_inst_2895_: *mut crate::leanh::LeanObject,
    mut v_inst_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2897_ = crate::leanh::lean_ctor_get(v_inst_2894_, 0);
    v_toBind_2898_ = crate::leanh::lean_ctor_get(v_inst_2894_, 1);
    crate::leanh::lean_inc_n(v_toBind_2898_, 3);
    v_getSemiring_2899_ = crate::leanh::lean_ctor_get(v_inst_2896_, 0);
    crate::leanh::lean_inc(v_getSemiring_2899_);
    v_modifySemiring_2900_ = crate::leanh::lean_ctor_get(v_inst_2896_, 1);
    crate::leanh::lean_inc(v_modifySemiring_2900_);
    crate::leanh::lean_dec_ref(v_inst_2896_);
    v_toPure_2901_ = crate::leanh::lean_ctor_get(v_toApplicative_2897_, 1);
    crate::leanh::lean_inc_n(v_toPure_2901_, 2);
    v___f_2902_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2902_, 0, v_toPure_2901_);
    crate::leanh::lean_closure_set(v___f_2902_, 1, v_modifySemiring_2900_);
    crate::leanh::lean_closure_set(v___f_2902_, 2, v_toBind_2898_);
    v___f_2903_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2903_, 0, v_toPure_2901_);
    crate::leanh::lean_closure_set(v___f_2903_, 1, v_inst_2893_);
    crate::leanh::lean_closure_set(v___f_2903_, 2, v_inst_2894_);
    crate::leanh::lean_closure_set(v___f_2903_, 3, v_inst_2895_);
    crate::leanh::lean_closure_set(v___f_2903_, 4, v_toBind_2898_);
    crate::leanh::lean_closure_set(v___f_2903_, 5, v___f_2902_);
    v___x_2904_ = crate::leanh::lean_apply_4(
        v_toBind_2898_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_2899_,
        v___f_2903_,
    );
    return v___x_2904_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27(
    mut v_m_2905_: *mut crate::leanh::LeanObject,
    mut v_inst_2906_: *mut crate::leanh::LeanObject,
    mut v_inst_2907_: *mut crate::leanh::LeanObject,
    mut v_inst_2908_: *mut crate::leanh::LeanObject,
    mut v_inst_2909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2910_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(
        v_inst_2906_,
        v_inst_2907_,
        v_inst_2908_,
        v_inst_2909_,
    );
    return v___x_2910_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Functions(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Functions(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Functions(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Functions(builtin);
}

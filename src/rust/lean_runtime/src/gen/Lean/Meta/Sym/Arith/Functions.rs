// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Functions
// Imports: Lean.Meta.Sym.Arith.MonadRing Lean.Meta.Sym.Arith.MonadSemiring
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
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
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [101, 114, 114, 111, 114, 32, 119, 104, 105, 108, 101, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 105, 110, 103, 32, 97, 114, 105, 116, 104, 109, 101, 116, 105, 99, 32, 111, 112, 101, 114, 97, 116, 111, 114, 115, 58, 10, 105, 110, 115, 116, 97, 110, 99, 101, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 32, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_value: LeanStringObject<59> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 59, m_capacity: 59, m_length: 58, m_data: [10, 119, 104, 101, 110, 32, 111, 110, 108, 121, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 97, 114, 101, 32, 114, 101, 100, 117, 99, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value) as *mut LeanObject,18388652353510661091 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value) as *mut LeanObject,12847922472053947547 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value) as *mut LeanObject,14765357657372582228 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value) as *mut LeanObject,5779414593499529281 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            9594062259507646949 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value: LeanStringObject<6> =
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
        m_data: [116, 111, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            5442360487226035463 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value: LeanStringObject<5> =
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
        m_data: [72, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value)
                as *mut LeanObject,
            10393083817453678557 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value: LeanStringObject<5> =
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
        m_data: [104, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value)
                as *mut LeanObject,
            10393083817453678557 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value)
                as *mut LeanObject,
            10680564408669940870 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            18134279130838690737 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value: LeanStringObject<6> =
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
        m_data: [116, 111, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            7102027102192867304 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value: LeanStringObject<5> =
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
        m_data: [72, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value)
                as *mut LeanObject,
            2929883540436775422 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value: LeanStringObject<5> =
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
        m_data: [104, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value)
                as *mut LeanObject,
            2929883540436775422 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value)
                as *mut LeanObject,
            1611444129324655608 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            10135981711945425184 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value: LeanStringObject<5> =
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
        m_data: [82, 105, 110, 103, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value: LeanStringObject<6> =
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
        m_data: [116, 111, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            10806710915646349764 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value)
                as *mut LeanObject,
            18169824201013588232 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value: LeanStringObject<5> =
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
        m_data: [72, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value)
                as *mut LeanObject,
            16856108565602861689 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value: LeanStringObject<5> =
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
        m_data: [104, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value)
                as *mut LeanObject,
            16856108565602861689 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value)
                as *mut LeanObject,
            4187025665268973031 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value: LeanStringObject<6> =
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
        m_data: [116, 111, 78, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            10806710915646349764 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            10040236838748678500 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value: LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value: LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value)
                as *mut LeanObject,
            17185717442815859305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value:
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
    m_data: [99, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value)
            as *mut LeanObject,
        7009148538150066493 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value)
            as *mut LeanObject,
        439118677539554485 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2:
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
            l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value)
            as *mut LeanObject,
        10806710915646349764 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value)
            as *mut LeanObject,
        14561037289535094017 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value)
            as *mut LeanObject,
        4977321555018234431 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value: LeanStringObject<6> =
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
        m_data: [70, 105, 101, 108, 100, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value: LeanStringObject<6> =
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
        m_data: [116, 111, 73, 110, 118, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            8615353994042975301 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value)
                as *mut LeanObject,
            7723290638220826725 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value: LeanStringObject<4> =
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
        m_data: [73, 110, 118, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value)
                as *mut LeanObject,
            1412621069384631438 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value: LeanStringObject<4> =
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
        m_data: [105, 110, 118, 0],
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value)
                as *mut LeanObject,
            1412621069384631438 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value)
                as *mut LeanObject,
            10171450186735820607 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value: LeanStringObject<
    36,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(
    mut v_msgData_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    v___x_1462_ = lean_st_ref_get(v___y_1460_);
    v_env_1463_ = lean_ctor_get(v___x_1462_, 0);
    lean_inc_ref(v_env_1463_);
    lean_dec(v___x_1462_);
    v___x_1464_ = lean_st_ref_get(v___y_1458_);
    v_mctx_1465_ = lean_ctor_get(v___x_1464_, 0);
    lean_inc_ref(v_mctx_1465_);
    lean_dec(v___x_1464_);
    v_lctx_1466_ = lean_ctor_get(v___y_1457_, 2);
    v_options_1467_ = lean_ctor_get(v___y_1459_, 2);
    lean_inc_ref(v_options_1467_);
    lean_inc_ref(v_lctx_1466_);
    v___x_1468_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1468_, 0, v_env_1463_);
    lean_ctor_set(v___x_1468_, 1, v_mctx_1465_);
    lean_ctor_set(v___x_1468_, 2, v_lctx_1466_);
    lean_ctor_set(v___x_1468_, 3, v_options_1467_);
    v___x_1469_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1469_, 0, v___x_1468_);
    lean_ctor_set(v___x_1469_, 1, v_msgData_1456_);
    v___x_1470_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1470_, 0, v___x_1469_);
    return v___x_1470_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(
    mut v_msgData_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1477_: *mut LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msgData_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
    lean_dec(v___y_1475_);
    lean_dec_ref(v___y_1474_);
    lean_dec(v___y_1473_);
    lean_dec_ref(v___y_1472_);
    return v_res_1477_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(
    mut v_msg_1478_: *mut LeanObject,
    mut v___y_1479_: *mut LeanObject,
    mut v___y_1480_: *mut LeanObject,
    mut v___y_1481_: *mut LeanObject,
    mut v___y_1482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1489_: u8 = 0;
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1484_ = lean_ctor_get(v___y_1481_, 5);
                v___x_1485_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
                v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
                v_isSharedCheck_1494_ = (!lean_is_exclusive(v___x_1485_)) as u8;
                if v_isSharedCheck_1494_ == 0 {
                    v___x_1488_ = v___x_1485_;
                    v_isShared_1489_ = v_isSharedCheck_1494_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1486_);
                    lean_dec(v___x_1485_);
                    v___x_1488_ = lean_box(0);
                    v_isShared_1489_ = v_isSharedCheck_1494_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1484_);
                v___x_1490_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1490_, 0, v_ref_1484_);
                lean_ctor_set(v___x_1490_, 1, v_a_1486_);
                if v_isShared_1489_ == 0 {
                    lean_ctor_set_tag(v___x_1488_, 1);
                    lean_ctor_set(v___x_1488_, 0, v___x_1490_);
                    v___x_1492_ = v___x_1488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
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
    mut v_msg_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
    lean_dec(v___y_1499_);
    lean_dec_ref(v___y_1498_);
    lean_dec(v___y_1497_);
    lean_dec_ref(v___y_1496_);
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
-> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1505_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1;
    v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4()
-> *mut LeanObject {
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    v___x_1508_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3;
    v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
    return v___x_1509_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6()
-> *mut LeanObject {
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    v___x_1511_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5;
    v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
    return v___x_1512_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8()
-> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ =
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7;
    v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
    return v___x_1515_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(
    mut v_declName_1516_: *mut LeanObject,
    mut v_inst_1517_: *mut LeanObject,
    mut v_inst_x27_1518_: *mut LeanObject,
    mut v_a_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
    mut v_a_1522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1545_: u8 = 0;
    let mut v_trackZetaDelta_1546_: u8 = 0;
    let mut v_zetaDeltaSet_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1553_: u8 = 0;
    let mut v_inTypeClassResolution_1554_: u8 = 0;
    let mut v_cacheInferType_1555_: u8 = 0;
    let mut v___x_1556_: u8 = 0;
    let mut v_config_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u64 = 0;
    let mut v___x_1560_: u64 = 0;
    let mut v___x_1561_: u64 = 0;
    let mut v___x_1562_: u64 = 0;
    let mut v___x_1563_: u64 = 0;
    let mut v_key_1564_: u64 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1572_: u8 = 0;
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_a_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_reuseFailAlloc_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1524_ = l_Lean_Meta_Context_config(v_a_1519_);
                v_foApprox_1525_ = lean_ctor_get_uint8(v___x_1524_, 0 as u32);
                v_ctxApprox_1526_ = lean_ctor_get_uint8(v___x_1524_, 1 as u32);
                v_quasiPatternApprox_1527_ = lean_ctor_get_uint8(v___x_1524_, 2 as u32);
                v_constApprox_1528_ = lean_ctor_get_uint8(v___x_1524_, 3 as u32);
                v_isDefEqStuckEx_1529_ = lean_ctor_get_uint8(v___x_1524_, 4 as u32);
                v_unificationHints_1530_ = lean_ctor_get_uint8(v___x_1524_, 5 as u32);
                v_proofIrrelevance_1531_ = lean_ctor_get_uint8(v___x_1524_, 6 as u32);
                v_assignSyntheticOpaque_1532_ = lean_ctor_get_uint8(v___x_1524_, 7 as u32);
                v_offsetCnstrs_1533_ = lean_ctor_get_uint8(v___x_1524_, 8 as u32);
                v_etaStruct_1534_ = lean_ctor_get_uint8(v___x_1524_, 10 as u32);
                v_univApprox_1535_ = lean_ctor_get_uint8(v___x_1524_, 11 as u32);
                v_iota_1536_ = lean_ctor_get_uint8(v___x_1524_, 12 as u32);
                v_beta_1537_ = lean_ctor_get_uint8(v___x_1524_, 13 as u32);
                v_proj_1538_ = lean_ctor_get_uint8(v___x_1524_, 14 as u32);
                v_zeta_1539_ = lean_ctor_get_uint8(v___x_1524_, 15 as u32);
                v_zetaDelta_1540_ = lean_ctor_get_uint8(v___x_1524_, 16 as u32);
                v_zetaUnused_1541_ = lean_ctor_get_uint8(v___x_1524_, 17 as u32);
                v_zetaHave_1542_ = lean_ctor_get_uint8(v___x_1524_, 18 as u32);
                v_isSharedCheck_1601_ = (!lean_is_exclusive(v___x_1524_)) as u8;
                if v_isSharedCheck_1601_ == 0 {
                    v___x_1544_ = v___x_1524_;
                    v_isShared_1545_ = v_isSharedCheck_1601_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_1524_);
                    v___x_1544_ = lean_box(0);
                    v_isShared_1545_ = v_isSharedCheck_1601_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_1546_ = lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1547_ = lean_ctor_get(v_a_1519_, 1);
                v_lctx_1548_ = lean_ctor_get(v_a_1519_, 2);
                v_localInstances_1549_ = lean_ctor_get(v_a_1519_, 3);
                v_defEqCtx_x3f_1550_ = lean_ctor_get(v_a_1519_, 4);
                v_synthPendingDepth_1551_ = lean_ctor_get(v_a_1519_, 5);
                v_canUnfold_x3f_1552_ = lean_ctor_get(v_a_1519_, 6);
                v_univApprox_1553_ = lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1554_ = lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1555_ = lean_ctor_get_uint8(
                    v_a_1519_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_1556_ = 3;
                if v_isShared_1545_ == 0 {
                    v_config_1558_ = v___x_1544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 0 as u32, v_foApprox_1525_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 1 as u32, v_ctxApprox_1526_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        2 as u32,
                        v_quasiPatternApprox_1527_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 3 as u32, v_constApprox_1528_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 4 as u32, v_isDefEqStuckEx_1529_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 5 as u32, v_unificationHints_1530_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 6 as u32, v_proofIrrelevance_1531_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1600_,
                        7 as u32,
                        v_assignSyntheticOpaque_1532_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 8 as u32, v_offsetCnstrs_1533_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 10 as u32, v_etaStruct_1534_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 11 as u32, v_univApprox_1535_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 12 as u32, v_iota_1536_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 13 as u32, v_beta_1537_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 14 as u32, v_proj_1538_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 15 as u32, v_zeta_1539_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 16 as u32, v_zetaDelta_1540_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 17 as u32, v_zetaUnused_1541_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1600_, 18 as u32, v_zetaHave_1542_);
                    v_config_1558_ = v_reuseFailAlloc_1600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_1558_, 9 as u32, v___x_1556_);
                v___x_1559_ = l_Lean_Meta_Context_configKey(v_a_1519_);
                v___x_1560_ = 3u64;
                v___x_1561_ = lean_uint64_shift_right(v___x_1559_, v___x_1560_);
                v___x_1562_ = lean_uint64_shift_left(v___x_1561_, v___x_1560_);
                v___x_1563_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0);
                v_key_1564_ = lean_uint64_lor(v___x_1562_, v___x_1563_);
                v___x_1565_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_1565_, 0, v_config_1558_);
                lean_ctor_set_uint64(
                    v___x_1565_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_1564_,
                );
                lean_inc(v_canUnfold_x3f_1552_);
                lean_inc(v_synthPendingDepth_1551_);
                lean_inc(v_defEqCtx_x3f_1550_);
                lean_inc_ref(v_localInstances_1549_);
                lean_inc_ref(v_lctx_1548_);
                lean_inc(v_zetaDeltaSet_1547_);
                v___x_1566_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_1566_, 0, v___x_1565_);
                lean_ctor_set(v___x_1566_, 1, v_zetaDeltaSet_1547_);
                lean_ctor_set(v___x_1566_, 2, v_lctx_1548_);
                lean_ctor_set(v___x_1566_, 3, v_localInstances_1549_);
                lean_ctor_set(v___x_1566_, 4, v_defEqCtx_x3f_1550_);
                lean_ctor_set(v___x_1566_, 5, v_synthPendingDepth_1551_);
                lean_ctor_set(v___x_1566_, 6, v_canUnfold_x3f_1552_);
                lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1546_,
                );
                lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1553_,
                );
                lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1554_,
                );
                lean_ctor_set_uint8(
                    v___x_1566_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1555_,
                );
                lean_inc_ref(v_inst_x27_1518_);
                lean_inc_ref(v_inst_1517_);
                v___x_1567_ = l_Lean_Meta_isExprDefEq(
                    v_inst_1517_,
                    v_inst_x27_1518_,
                    v___x_1566_,
                    v_a_1520_,
                    v_a_1521_,
                    v_a_1522_,
                );
                lean_dec_ref_known(v___x_1566_, 7);
                if lean_obj_tag(v___x_1567_) == 0 {
                    v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
                    v_isSharedCheck_1591_ = (!lean_is_exclusive(v___x_1567_)) as u8;
                    if v_isSharedCheck_1591_ == 0 {
                        v___x_1570_ = v___x_1567_;
                        v_isShared_1571_ = v_isSharedCheck_1591_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1568_);
                        lean_dec(v___x_1567_);
                        v___x_1570_ = lean_box(0);
                        v_isShared_1571_ = v_isSharedCheck_1591_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_x27_1518_);
                    lean_dec_ref(v_inst_1517_);
                    lean_dec(v_declName_1516_);
                    v_a_1592_ = lean_ctor_get(v___x_1567_, 0);
                    v_isSharedCheck_1599_ = (!lean_is_exclusive(v___x_1567_)) as u8;
                    if v_isSharedCheck_1599_ == 0 {
                        v___x_1594_ = v___x_1567_;
                        v_isShared_1595_ = v_isSharedCheck_1599_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1592_);
                        lean_dec(v___x_1567_);
                        v___x_1594_ = lean_box(0);
                        v_isShared_1595_ = v_isSharedCheck_1599_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1572_ = (lean_unbox(v_a_1568_) as u8);
                lean_dec(v_a_1568_);
                if v___x_1572_ == 0 {
                    lean_del_object(v___x_1570_);
                    v___x_1573_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2);
                    v___x_1574_ = l_Lean_MessageData_ofName(v_declName_1516_);
                    v___x_1575_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1575_, 0, v___x_1573_);
                    lean_ctor_set(v___x_1575_, 1, v___x_1574_);
                    v___x_1576_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4);
                    v___x_1577_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1577_, 0, v___x_1575_);
                    lean_ctor_set(v___x_1577_, 1, v___x_1576_);
                    v___x_1578_ = l_Lean_indentExpr(v_inst_1517_);
                    v___x_1579_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1579_, 0, v___x_1577_);
                    lean_ctor_set(v___x_1579_, 1, v___x_1578_);
                    v___x_1580_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6);
                    v___x_1581_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1581_, 0, v___x_1579_);
                    lean_ctor_set(v___x_1581_, 1, v___x_1580_);
                    v___x_1582_ = l_Lean_indentExpr(v_inst_x27_1518_);
                    v___x_1583_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1583_, 0, v___x_1581_);
                    lean_ctor_set(v___x_1583_, 1, v___x_1582_);
                    v___x_1584_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8);
                    v___x_1585_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1585_, 0, v___x_1583_);
                    lean_ctor_set(v___x_1585_, 1, v___x_1584_);
                    v___x_1586_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_1585_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
                    return v___x_1586_;
                } else {
                    lean_dec_ref(v_inst_x27_1518_);
                    lean_dec_ref(v_inst_1517_);
                    lean_dec(v_declName_1516_);
                    v___x_1587_ = lean_box(0);
                    if v_isShared_1571_ == 0 {
                        lean_ctor_set(v___x_1570_, 0, v___x_1587_);
                        v___x_1589_ = v___x_1570_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
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
                    v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
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
    mut v_declName_1602_: *mut LeanObject,
    mut v_inst_1603_: *mut LeanObject,
    mut v_inst_x27_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
    mut v_a_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1610_: *mut LeanObject = core::ptr::null_mut();
    v_res_1610_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(
        v_declName_1602_,
        v_inst_1603_,
        v_inst_x27_1604_,
        v_a_1605_,
        v_a_1606_,
        v_a_1607_,
        v_a_1608_,
    );
    lean_dec(v_a_1608_);
    lean_dec_ref(v_a_1607_);
    lean_dec(v_a_1606_);
    lean_dec_ref(v_a_1605_);
    return v_res_1610_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(
    mut v_00_u03b1_1611_: *mut LeanObject,
    mut v_msg_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
    return v___x_1618_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(
    mut v_00_u03b1_1619_: *mut LeanObject,
    mut v_msg_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1626_: *mut LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_1619_, v_msg_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
    lean_dec(v___y_1624_);
    lean_dec_ref(v___y_1623_);
    lean_dec(v___y_1622_);
    lean_dec_ref(v___y_1621_);
    return v_res_1626_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(
    mut v_inst_1627_: *mut LeanObject,
    mut v_declName_1628_: *mut LeanObject,
    mut v___x_1629_: *mut LeanObject,
    mut v_type_1630_: *mut LeanObject,
    mut v_inst_1631_: *mut LeanObject,
    mut v_____r_1632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    v_canonExpr_1633_ = lean_ctor_get(v_inst_1627_, 0);
    lean_inc(v_canonExpr_1633_);
    lean_dec_ref(v_inst_1627_);
    v___x_1634_ = l_Lean_mkConst(v_declName_1628_, v___x_1629_);
    v___x_1635_ = l_Lean_mkAppB(v___x_1634_, v_type_1630_, v_inst_1631_);
    v___x_1636_ = lean_apply_1(v_canonExpr_1633_, v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(
    mut v_inst_1637_: *mut LeanObject,
    mut v_declName_1638_: *mut LeanObject,
    mut v___x_1639_: *mut LeanObject,
    mut v_type_1640_: *mut LeanObject,
    mut v_expectedInst_1641_: *mut LeanObject,
    mut v_inst_1642_: *mut LeanObject,
    mut v_toBind_1643_: *mut LeanObject,
    mut v_inst_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1644_);
    lean_inc(v_declName_1638_);
    v___f_1645_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1645_, 0, v_inst_1637_);
    lean_closure_set(v___f_1645_, 1, v_declName_1638_);
    lean_closure_set(v___f_1645_, 2, v___x_1639_);
    lean_closure_set(v___f_1645_, 3, v_type_1640_);
    lean_closure_set(v___f_1645_, 4, v_inst_1644_);
    v___x_1646_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1646_, 0, v_declName_1638_);
    lean_closure_set(v___x_1646_, 1, v_inst_1644_);
    lean_closure_set(v___x_1646_, 2, v_expectedInst_1641_);
    v___x_1647_ = lean_apply_2(v_inst_1642_, lean_box(0), v___x_1646_);
    v___x_1648_ = lean_apply_4(
        v_toBind_1643_,
        lean_box(0),
        lean_box(0),
        v___x_1647_,
        v___f_1645_,
    );
    return v___x_1648_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(
    mut v_inst_1649_: *mut LeanObject,
    mut v_inst_1650_: *mut LeanObject,
    mut v_inst_1651_: *mut LeanObject,
    mut v_inst_1652_: *mut LeanObject,
    mut v_type_1653_: *mut LeanObject,
    mut v_u_1654_: *mut LeanObject,
    mut v_instDeclName_1655_: *mut LeanObject,
    mut v_declName_1656_: *mut LeanObject,
    mut v_expectedInst_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1658_ = lean_ctor_get(v_inst_1651_, 1);
    lean_inc_n(v_toBind_1658_, 2);
    v___x_1659_ = lean_box(0);
    v___x_1660_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1660_, 0, v_u_1654_);
    lean_ctor_set(v___x_1660_, 1, v___x_1659_);
    lean_inc_ref(v_type_1653_);
    lean_inc_ref(v___x_1660_);
    lean_inc_ref(v_inst_1652_);
    v___f_1661_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1
            as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1661_, 0, v_inst_1652_);
    lean_closure_set(v___f_1661_, 1, v_declName_1656_);
    lean_closure_set(v___f_1661_, 2, v___x_1660_);
    lean_closure_set(v___f_1661_, 3, v_type_1653_);
    lean_closure_set(v___f_1661_, 4, v_expectedInst_1657_);
    lean_closure_set(v___f_1661_, 5, v_inst_1649_);
    lean_closure_set(v___f_1661_, 6, v_toBind_1658_);
    v___x_1662_ = l_Lean_mkConst(v_instDeclName_1655_, v___x_1660_);
    v___x_1663_ = l_Lean_Expr_app___override(v___x_1662_, v_type_1653_);
    v___x_1664_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1651_,
        v_inst_1650_,
        v_inst_1652_,
        v___x_1663_,
    );
    v___x_1665_ = lean_apply_4(
        v_toBind_1658_,
        lean_box(0),
        lean_box(0),
        v___x_1664_,
        v___f_1661_,
    );
    return v___x_1665_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(
    mut v_m_1666_: *mut LeanObject,
    mut v_inst_1667_: *mut LeanObject,
    mut v_inst_1668_: *mut LeanObject,
    mut v_inst_1669_: *mut LeanObject,
    mut v_inst_1670_: *mut LeanObject,
    mut v_type_1671_: *mut LeanObject,
    mut v_u_1672_: *mut LeanObject,
    mut v_instDeclName_1673_: *mut LeanObject,
    mut v_declName_1674_: *mut LeanObject,
    mut v_expectedInst_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1677_: *mut LeanObject,
    mut v_declName_1678_: *mut LeanObject,
    mut v___x_1679_: *mut LeanObject,
    mut v_type_1680_: *mut LeanObject,
    mut v_inst_1681_: *mut LeanObject,
    mut v_____r_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    v_canonExpr_1683_ = lean_ctor_get(v_inst_1677_, 0);
    lean_inc(v_canonExpr_1683_);
    lean_dec_ref(v_inst_1677_);
    v___x_1684_ = l_Lean_mkConst(v_declName_1678_, v___x_1679_);
    lean_inc_ref_n(v_type_1680_, 2);
    v___x_1685_ = l_Lean_mkApp4(
        v___x_1684_,
        v_type_1680_,
        v_type_1680_,
        v_type_1680_,
        v_inst_1681_,
    );
    v___x_1686_ = lean_apply_1(v_canonExpr_1683_, v___x_1685_);
    return v___x_1686_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(
    mut v_inst_1687_: *mut LeanObject,
    mut v_declName_1688_: *mut LeanObject,
    mut v___x_1689_: *mut LeanObject,
    mut v_type_1690_: *mut LeanObject,
    mut v_expectedInst_1691_: *mut LeanObject,
    mut v_inst_1692_: *mut LeanObject,
    mut v_toBind_1693_: *mut LeanObject,
    mut v_inst_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1694_);
    lean_inc(v_declName_1688_);
    v___f_1695_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_1695_, 0, v_inst_1687_);
    lean_closure_set(v___f_1695_, 1, v_declName_1688_);
    lean_closure_set(v___f_1695_, 2, v___x_1689_);
    lean_closure_set(v___f_1695_, 3, v_type_1690_);
    lean_closure_set(v___f_1695_, 4, v_inst_1694_);
    v___x_1696_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1696_, 0, v_declName_1688_);
    lean_closure_set(v___x_1696_, 1, v_inst_1694_);
    lean_closure_set(v___x_1696_, 2, v_expectedInst_1691_);
    v___x_1697_ = lean_apply_2(v_inst_1692_, lean_box(0), v___x_1696_);
    v___x_1698_ = lean_apply_4(
        v_toBind_1693_,
        lean_box(0),
        lean_box(0),
        v___x_1697_,
        v___f_1695_,
    );
    return v___x_1698_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(
    mut v_inst_1699_: *mut LeanObject,
    mut v_inst_1700_: *mut LeanObject,
    mut v_inst_1701_: *mut LeanObject,
    mut v_inst_1702_: *mut LeanObject,
    mut v_type_1703_: *mut LeanObject,
    mut v_u_1704_: *mut LeanObject,
    mut v_instDeclName_1705_: *mut LeanObject,
    mut v_declName_1706_: *mut LeanObject,
    mut v_expectedInst_1707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1708_ = lean_ctor_get(v_inst_1701_, 1);
    lean_inc_n(v_toBind_1708_, 2);
    v___x_1709_ = lean_box(0);
    lean_inc_n(v_u_1704_, 2);
    v___x_1710_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1710_, 0, v_u_1704_);
    lean_ctor_set(v___x_1710_, 1, v___x_1709_);
    v___x_1711_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1711_, 0, v_u_1704_);
    lean_ctor_set(v___x_1711_, 1, v___x_1710_);
    v___x_1712_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1712_, 0, v_u_1704_);
    lean_ctor_set(v___x_1712_, 1, v___x_1711_);
    lean_inc_ref_n(v_type_1703_, 3);
    lean_inc_ref(v___x_1712_);
    lean_inc_ref(v_inst_1702_);
    v___f_1713_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1 as *mut core::ffi::c_void, 8, 7);
    lean_closure_set(v___f_1713_, 0, v_inst_1702_);
    lean_closure_set(v___f_1713_, 1, v_declName_1706_);
    lean_closure_set(v___f_1713_, 2, v___x_1712_);
    lean_closure_set(v___f_1713_, 3, v_type_1703_);
    lean_closure_set(v___f_1713_, 4, v_expectedInst_1707_);
    lean_closure_set(v___f_1713_, 5, v_inst_1699_);
    lean_closure_set(v___f_1713_, 6, v_toBind_1708_);
    v___x_1714_ = l_Lean_mkConst(v_instDeclName_1705_, v___x_1712_);
    v___x_1715_ = l_Lean_mkApp3(v___x_1714_, v_type_1703_, v_type_1703_, v_type_1703_);
    v___x_1716_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1701_,
        v_inst_1700_,
        v_inst_1702_,
        v___x_1715_,
    );
    v___x_1717_ = lean_apply_4(
        v_toBind_1708_,
        lean_box(0),
        lean_box(0),
        v___x_1716_,
        v___f_1713_,
    );
    return v___x_1717_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(
    mut v_m_1718_: *mut LeanObject,
    mut v_inst_1719_: *mut LeanObject,
    mut v_inst_1720_: *mut LeanObject,
    mut v_inst_1721_: *mut LeanObject,
    mut v_inst_1722_: *mut LeanObject,
    mut v_type_1723_: *mut LeanObject,
    mut v_u_1724_: *mut LeanObject,
    mut v_instDeclName_1725_: *mut LeanObject,
    mut v_declName_1726_: *mut LeanObject,
    mut v_expectedInst_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1729_: *mut LeanObject,
    mut v___x_1730_: *mut LeanObject,
    mut v___x_1731_: *mut LeanObject,
    mut v_type_1732_: *mut LeanObject,
    mut v___x_1733_: *mut LeanObject,
    mut v_inst_1734_: *mut LeanObject,
    mut v_____r_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    v_canonExpr_1736_ = lean_ctor_get(v_inst_1729_, 0);
    lean_inc(v_canonExpr_1736_);
    lean_dec_ref(v_inst_1729_);
    v___x_1737_ = l_Lean_mkConst(v___x_1730_, v___x_1731_);
    lean_inc_ref(v_type_1732_);
    v___x_1738_ = l_Lean_mkApp4(
        v___x_1737_,
        v_type_1732_,
        v___x_1733_,
        v_type_1732_,
        v_inst_1734_,
    );
    v___x_1739_ = lean_apply_1(v_canonExpr_1736_, v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(
    mut v___x_1750_: *mut LeanObject,
    mut v_type_1751_: *mut LeanObject,
    mut v_semiringInst_1752_: *mut LeanObject,
    mut v___x_1753_: *mut LeanObject,
    mut v_inst_1754_: *mut LeanObject,
    mut v___x_1755_: *mut LeanObject,
    mut v___x_1756_: *mut LeanObject,
    mut v_inst_1757_: *mut LeanObject,
    mut v_toBind_1758_: *mut LeanObject,
    mut v_inst_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    v___x_1760_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4;
    v___x_1761_ = l_Lean_mkConst(v___x_1760_, v___x_1750_);
    lean_inc_ref(v_type_1751_);
    v_inst_x27_1762_ = l_Lean_mkAppB(v___x_1761_, v_type_1751_, v_semiringInst_1752_);
    v___x_1763_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5;
    v___x_1764_ = l_Lean_Name_mkStr2(v___x_1753_, v___x_1763_);
    lean_inc_ref(v_inst_1759_);
    lean_inc(v___x_1764_);
    v___f_1765_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0
            as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1765_, 0, v_inst_1754_);
    lean_closure_set(v___f_1765_, 1, v___x_1764_);
    lean_closure_set(v___f_1765_, 2, v___x_1755_);
    lean_closure_set(v___f_1765_, 3, v_type_1751_);
    lean_closure_set(v___f_1765_, 4, v___x_1756_);
    lean_closure_set(v___f_1765_, 5, v_inst_1759_);
    v___x_1766_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1766_, 0, v___x_1764_);
    lean_closure_set(v___x_1766_, 1, v_inst_1759_);
    lean_closure_set(v___x_1766_, 2, v_inst_x27_1762_);
    v___x_1767_ = lean_apply_2(v_inst_1757_, lean_box(0), v___x_1766_);
    v___x_1768_ = lean_apply_4(
        v_toBind_1758_,
        lean_box(0),
        lean_box(0),
        v___x_1767_,
        v___f_1765_,
    );
    return v___x_1768_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    v___x_1772_ = lean_unsigned_to_nat(0);
    v___x_1773_ = l_Lean_Level_ofNat(v___x_1772_);
    return v___x_1773_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(
    mut v_inst_1774_: *mut LeanObject,
    mut v_inst_1775_: *mut LeanObject,
    mut v_inst_1776_: *mut LeanObject,
    mut v_inst_1777_: *mut LeanObject,
    mut v_u_1778_: *mut LeanObject,
    mut v_type_1779_: *mut LeanObject,
    mut v_semiringInst_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1781_ = lean_ctor_get(v_inst_1776_, 1);
    lean_inc_n(v_toBind_1781_, 2);
    v___x_1782_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0;
    v___x_1783_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1;
    v___x_1784_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once), _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
    v___x_1785_ = lean_box(0);
    lean_inc(v_u_1778_);
    v___x_1786_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1786_, 0, v_u_1778_);
    lean_ctor_set(v___x_1786_, 1, v___x_1785_);
    lean_inc_ref(v___x_1786_);
    v___x_1787_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1787_, 0, v___x_1784_);
    lean_ctor_set(v___x_1787_, 1, v___x_1786_);
    v___x_1788_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1788_, 0, v_u_1778_);
    lean_ctor_set(v___x_1788_, 1, v___x_1787_);
    lean_inc_ref(v___x_1788_);
    v___x_1789_ = l_Lean_mkConst(v___x_1783_, v___x_1788_);
    v___x_1790_ = l_Lean_Nat_mkType;
    lean_inc_ref(v_inst_1777_);
    lean_inc_ref_n(v_type_1779_, 2);
    v___f_1791_ = lean_alloc_closure(
        l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1
            as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_1791_, 0, v___x_1786_);
    lean_closure_set(v___f_1791_, 1, v_type_1779_);
    lean_closure_set(v___f_1791_, 2, v_semiringInst_1780_);
    lean_closure_set(v___f_1791_, 3, v___x_1782_);
    lean_closure_set(v___f_1791_, 4, v_inst_1777_);
    lean_closure_set(v___f_1791_, 5, v___x_1788_);
    lean_closure_set(v___f_1791_, 6, v___x_1790_);
    lean_closure_set(v___f_1791_, 7, v_inst_1774_);
    lean_closure_set(v___f_1791_, 8, v_toBind_1781_);
    v___x_1792_ = l_Lean_mkApp3(v___x_1789_, v_type_1779_, v___x_1790_, v_type_1779_);
    v___x_1793_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1776_,
        v_inst_1775_,
        v_inst_1777_,
        v___x_1792_,
    );
    v___x_1794_ = lean_apply_4(
        v_toBind_1781_,
        lean_box(0),
        lean_box(0),
        v___x_1793_,
        v___f_1791_,
    );
    return v___x_1794_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(
    mut v_m_1795_: *mut LeanObject,
    mut v_inst_1796_: *mut LeanObject,
    mut v_inst_1797_: *mut LeanObject,
    mut v_inst_1798_: *mut LeanObject,
    mut v_inst_1799_: *mut LeanObject,
    mut v_u_1800_: *mut LeanObject,
    mut v_type_1801_: *mut LeanObject,
    mut v_semiringInst_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_1804_: *mut LeanObject,
    mut v___x_1805_: *mut LeanObject,
    mut v___x_1806_: *mut LeanObject,
    mut v_type_1807_: *mut LeanObject,
    mut v_canonExpr_1808_: *mut LeanObject,
    mut v_inst_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    v___x_1810_ = l_Lean_Name_mkStr2(v___x_1804_, v___x_1805_);
    v___x_1811_ = l_Lean_mkConst(v___x_1810_, v___x_1806_);
    v___x_1812_ = l_Lean_mkAppB(v___x_1811_, v_type_1807_, v_inst_1809_);
    v___x_1813_ = lean_apply_1(v_canonExpr_1808_, v___x_1812_);
    return v___x_1813_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(
    mut v___f_1814_: *mut LeanObject,
    mut v_inst_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    v___x_1816_ = lean_apply_1(v___f_1814_, v_inst_1815_);
    return v___x_1816_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(
    mut v_toPure_1817_: *mut LeanObject,
    mut v_val_1818_: *mut LeanObject,
    mut v_toBind_1819_: *mut LeanObject,
    mut v___f_1820_: *mut LeanObject,
    mut v_____r_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = lean_apply_2(v_toPure_1817_, lean_box(0), v_val_1818_);
    v___x_1823_ = lean_apply_4(
        v_toBind_1819_,
        lean_box(0),
        lean_box(0),
        v___x_1822_,
        v___f_1820_,
    );
    return v___x_1823_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(
    mut v_toPure_1824_: *mut LeanObject,
    mut v_inst_x27_1825_: *mut LeanObject,
    mut v_toBind_1826_: *mut LeanObject,
    mut v___f_1827_: *mut LeanObject,
    mut v___f_1828_: *mut LeanObject,
    mut v___x_1829_: *mut LeanObject,
    mut v___x_1830_: *mut LeanObject,
    mut v_inst_1831_: *mut LeanObject,
    mut v_____do__lift_1832_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1832_) == 0 {
        let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_1831_);
        lean_dec_ref(v___x_1830_);
        lean_dec_ref(v___x_1829_);
        lean_dec(v___f_1828_);
        v___x_1833_ = lean_apply_2(v_toPure_1824_, lean_box(0), v_inst_x27_1825_);
        v___x_1834_ = lean_apply_4(
            v_toBind_1826_,
            lean_box(0),
            lean_box(0),
            v___x_1833_,
            v___f_1827_,
        );
        return v___x_1834_;
    } else {
        let mut v_val_1835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_1827_);
        v_val_1835_ = lean_ctor_get(v_____do__lift_1832_, 0);
        lean_inc_n(v_val_1835_, 2);
        lean_dec_ref_known(v_____do__lift_1832_, 1);
        lean_inc(v_toBind_1826_);
        v___f_1836_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___f_1836_, 0, v_toPure_1824_);
        lean_closure_set(v___f_1836_, 1, v_val_1835_);
        lean_closure_set(v___f_1836_, 2, v_toBind_1826_);
        lean_closure_set(v___f_1836_, 3, v___f_1828_);
        v___x_1837_ = l_Lean_Name_mkStr2(v___x_1829_, v___x_1830_);
        v___x_1838_ = lean_alloc_closure(
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
                as *mut core::ffi::c_void,
            8,
            3,
        );
        lean_closure_set(v___x_1838_, 0, v___x_1837_);
        lean_closure_set(v___x_1838_, 1, v_val_1835_);
        lean_closure_set(v___x_1838_, 2, v_inst_x27_1825_);
        v___x_1839_ = lean_apply_2(v_inst_1831_, lean_box(0), v___x_1838_);
        v___x_1840_ = lean_apply_4(
            v_toBind_1826_,
            lean_box(0),
            lean_box(0),
            v___x_1839_,
            v___f_1836_,
        );
        return v___x_1840_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(
    mut v_inst_1850_: *mut LeanObject,
    mut v_inst_1851_: *mut LeanObject,
    mut v_inst_1852_: *mut LeanObject,
    mut v_u_1853_: *mut LeanObject,
    mut v_type_1854_: *mut LeanObject,
    mut v_semiringInst_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v_toPure_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instType_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1856_ = lean_ctor_get(v_inst_1851_, 0);
                lean_inc_ref(v_toApplicative_1856_);
                v_toBind_1857_ = lean_ctor_get(v_inst_1851_, 1);
                lean_inc(v_toBind_1857_);
                lean_dec_ref(v_inst_1851_);
                v_canonExpr_1858_ = lean_ctor_get(v_inst_1852_, 0);
                v_synthInstance_x3f_1859_ = lean_ctor_get(v_inst_1852_, 1);
                v_isSharedCheck_1881_ = (!lean_is_exclusive(v_inst_1852_)) as u8;
                if v_isSharedCheck_1881_ == 0 {
                    v___x_1861_ = v_inst_1852_;
                    v_isShared_1862_ = v_isSharedCheck_1881_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_synthInstance_x3f_1859_);
                    lean_inc(v_canonExpr_1858_);
                    lean_dec(v_inst_1852_);
                    v___x_1861_ = lean_box(0);
                    v_isShared_1862_ = v_isSharedCheck_1881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1863_ = lean_ctor_get(v_toApplicative_1856_, 1);
                lean_inc(v_toPure_1863_);
                lean_dec_ref(v_toApplicative_1856_);
                v___x_1864_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0;
                v___x_1865_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1;
                v___x_1866_ = lean_box(0);
                if v_isShared_1862_ == 0 {
                    lean_ctor_set_tag(v___x_1861_, 1);
                    lean_ctor_set(v___x_1861_, 1, v___x_1866_);
                    lean_ctor_set(v___x_1861_, 0, v_u_1853_);
                    v___x_1868_ = v___x_1861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_u_1853_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1866_);
                    v___x_1868_ = v_reuseFailAlloc_1880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v___x_1868_, 2);
                v___x_1869_ = l_Lean_mkConst(v___x_1865_, v___x_1868_);
                lean_inc_ref_n(v_type_1854_, 2);
                v_inst_x27_1870_ = l_Lean_mkAppB(v___x_1869_, v_type_1854_, v_semiringInst_1855_);
                v___x_1871_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2;
                v___f_1872_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___f_1872_, 0, v___x_1871_);
                lean_closure_set(v___f_1872_, 1, v___x_1864_);
                lean_closure_set(v___f_1872_, 2, v___x_1868_);
                lean_closure_set(v___f_1872_, 3, v_type_1854_);
                lean_closure_set(v___f_1872_, 4, v_canonExpr_1858_);
                v___f_1873_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1873_, 0, v___f_1872_);
                v___x_1874_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3;
                v___x_1875_ = l_Lean_mkConst(v___x_1874_, v___x_1868_);
                v_instType_1876_ = l_Lean_Expr_app___override(v___x_1875_, v_type_1854_);
                v___x_1877_ = lean_apply_1(v_synthInstance_x3f_1859_, v_instType_1876_);
                lean_inc_ref(v___f_1873_);
                lean_inc(v_toBind_1857_);
                v___f_1878_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2 as *mut core::ffi::c_void, 9, 8);
                lean_closure_set(v___f_1878_, 0, v_toPure_1863_);
                lean_closure_set(v___f_1878_, 1, v_inst_x27_1870_);
                lean_closure_set(v___f_1878_, 2, v_toBind_1857_);
                lean_closure_set(v___f_1878_, 3, v___f_1873_);
                lean_closure_set(v___f_1878_, 4, v___f_1873_);
                lean_closure_set(v___f_1878_, 5, v___x_1871_);
                lean_closure_set(v___f_1878_, 6, v___x_1864_);
                lean_closure_set(v___f_1878_, 7, v_inst_1850_);
                v___x_1879_ = lean_apply_4(
                    v_toBind_1857_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1882_: *mut LeanObject,
    mut v_inst_1883_: *mut LeanObject,
    mut v_inst_1884_: *mut LeanObject,
    mut v_inst_1885_: *mut LeanObject,
    mut v_u_1886_: *mut LeanObject,
    mut v_type_1887_: *mut LeanObject,
    mut v_semiringInst_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_addFn_1890_: *mut LeanObject,
    mut v_s_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut v_unused_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1892_ = lean_ctor_get(v_s_1891_, 0);
                v_type_1893_ = lean_ctor_get(v_s_1891_, 1);
                v_u_1894_ = lean_ctor_get(v_s_1891_, 2);
                v_ringInst_1895_ = lean_ctor_get(v_s_1891_, 3);
                v_semiringInst_1896_ = lean_ctor_get(v_s_1891_, 4);
                v_charInst_x3f_1897_ = lean_ctor_get(v_s_1891_, 5);
                v_mulFn_x3f_1898_ = lean_ctor_get(v_s_1891_, 7);
                v_subFn_x3f_1899_ = lean_ctor_get(v_s_1891_, 8);
                v_negFn_x3f_1900_ = lean_ctor_get(v_s_1891_, 9);
                v_powFn_x3f_1901_ = lean_ctor_get(v_s_1891_, 10);
                v_intCastFn_x3f_1902_ = lean_ctor_get(v_s_1891_, 11);
                v_natCastFn_x3f_1903_ = lean_ctor_get(v_s_1891_, 12);
                v_one_x3f_1904_ = lean_ctor_get(v_s_1891_, 13);
                v_isSharedCheck_1912_ = (!lean_is_exclusive(v_s_1891_)) as u8;
                if v_isSharedCheck_1912_ == 0 {
                    v_unused_1913_ = lean_ctor_get(v_s_1891_, 6);
                    lean_dec(v_unused_1913_);
                    v___x_1906_ = v_s_1891_;
                    v_isShared_1907_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_one_x3f_1904_);
                    lean_inc(v_natCastFn_x3f_1903_);
                    lean_inc(v_intCastFn_x3f_1902_);
                    lean_inc(v_powFn_x3f_1901_);
                    lean_inc(v_negFn_x3f_1900_);
                    lean_inc(v_subFn_x3f_1899_);
                    lean_inc(v_mulFn_x3f_1898_);
                    lean_inc(v_charInst_x3f_1897_);
                    lean_inc(v_semiringInst_1896_);
                    lean_inc(v_ringInst_1895_);
                    lean_inc(v_u_1894_);
                    lean_inc(v_type_1893_);
                    lean_inc(v_id_1892_);
                    lean_dec(v_s_1891_);
                    v___x_1906_ = lean_box(0);
                    v_isShared_1907_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1908_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1908_, 0, v_addFn_1890_);
                if v_isShared_1907_ == 0 {
                    lean_ctor_set(v___x_1906_, 6, v___x_1908_);
                    v___x_1910_ = v___x_1906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 14, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_id_1892_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_type_1893_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_u_1894_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_ringInst_1895_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_semiringInst_1896_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 5, v_charInst_x3f_1897_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 6, v___x_1908_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 7, v_mulFn_x3f_1898_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 8, v_subFn_x3f_1899_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 9, v_negFn_x3f_1900_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 10, v_powFn_x3f_1901_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 11, v_intCastFn_x3f_1902_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 12, v_natCastFn_x3f_1903_);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 13, v_one_x3f_1904_);
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
    mut v_toPure_1914_: *mut LeanObject,
    mut v_addFn_1915_: *mut LeanObject,
    mut v_____r_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917_ = lean_apply_2(v_toPure_1914_, lean_box(0), v_addFn_1915_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(
    mut v_toPure_1918_: *mut LeanObject,
    mut v_modifyRing_1919_: *mut LeanObject,
    mut v_toBind_1920_: *mut LeanObject,
    mut v_addFn_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_addFn_1921_);
    v___f_1922_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1922_, 0, v_addFn_1921_);
    v___f_1923_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1923_, 0, v_toPure_1918_);
    lean_closure_set(v___f_1923_, 1, v_addFn_1921_);
    v___x_1924_ = lean_apply_1(v_modifyRing_1919_, v___f_1922_);
    v___x_1925_ = lean_apply_4(
        v_toBind_1920_,
        lean_box(0),
        lean_box(0),
        v___x_1924_,
        v___f_1923_,
    );
    return v___x_1925_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(
    mut v_toPure_1942_: *mut LeanObject,
    mut v_inst_1943_: *mut LeanObject,
    mut v_inst_1944_: *mut LeanObject,
    mut v_inst_1945_: *mut LeanObject,
    mut v_inst_1946_: *mut LeanObject,
    mut v_toBind_1947_: *mut LeanObject,
    mut v___f_1948_: *mut LeanObject,
    mut v_ring_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addFn_x3f_1950_: *mut LeanObject = core::ptr::null_mut();
    v_addFn_x3f_1950_ = lean_ctor_get(v_ring_1949_, 6);
    if lean_obj_tag(v_addFn_x3f_1950_) == 1 {
        let mut v_val_1951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_addFn_x3f_1950_);
        lean_dec_ref(v_ring_1949_);
        lean_dec(v___f_1948_);
        lean_dec(v_toBind_1947_);
        lean_dec_ref(v_inst_1946_);
        lean_dec_ref(v_inst_1945_);
        lean_dec_ref(v_inst_1944_);
        lean_dec(v_inst_1943_);
        v_val_1951_ = lean_ctor_get(v_addFn_x3f_1950_, 0);
        lean_inc(v_val_1951_);
        lean_dec_ref_known(v_addFn_x3f_1950_, 1);
        v___x_1952_ = lean_apply_2(v_toPure_1942_, lean_box(0), v_val_1951_);
        return v___x_1952_;
    } else {
        let mut v_type_1953_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_1954_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1942_);
        v_type_1953_ = lean_ctor_get(v_ring_1949_, 1);
        lean_inc_ref_n(v_type_1953_, 3);
        v_u_1954_ = lean_ctor_get(v_ring_1949_, 2);
        lean_inc_n(v_u_1954_, 2);
        v_semiringInst_1955_ = lean_ctor_get(v_ring_1949_, 4);
        lean_inc_ref(v_semiringInst_1955_);
        lean_dec_ref(v_ring_1949_);
        v___x_1956_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1;
        v___x_1957_ = lean_box(0);
        v___x_1958_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1958_, 0, v_u_1954_);
        lean_ctor_set(v___x_1958_, 1, v___x_1957_);
        lean_inc_ref(v___x_1958_);
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
        v___x_1967_ = lean_apply_4(
            v_toBind_1947_,
            lean_box(0),
            lean_box(0),
            v___x_1966_,
            v___f_1948_,
        );
        return v___x_1967_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn___redArg(
    mut v_inst_1968_: *mut LeanObject,
    mut v_inst_1969_: *mut LeanObject,
    mut v_inst_1970_: *mut LeanObject,
    mut v_inst_1971_: *mut LeanObject,
    mut v_inst_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1973_ = lean_ctor_get(v_inst_1970_, 0);
    v_toBind_1974_ = lean_ctor_get(v_inst_1970_, 1);
    lean_inc_n(v_toBind_1974_, 3);
    v_getRing_1975_ = lean_ctor_get(v_inst_1972_, 0);
    lean_inc(v_getRing_1975_);
    v_modifyRing_1976_ = lean_ctor_get(v_inst_1972_, 1);
    lean_inc(v_modifyRing_1976_);
    lean_dec_ref(v_inst_1972_);
    v_toPure_1977_ = lean_ctor_get(v_toApplicative_1973_, 1);
    lean_inc_n(v_toPure_1977_, 2);
    v___f_1978_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1978_, 0, v_toPure_1977_);
    lean_closure_set(v___f_1978_, 1, v_modifyRing_1976_);
    lean_closure_set(v___f_1978_, 2, v_toBind_1974_);
    v___f_1979_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1979_, 0, v_toPure_1977_);
    lean_closure_set(v___f_1979_, 1, v_inst_1968_);
    lean_closure_set(v___f_1979_, 2, v_inst_1969_);
    lean_closure_set(v___f_1979_, 3, v_inst_1970_);
    lean_closure_set(v___f_1979_, 4, v_inst_1971_);
    lean_closure_set(v___f_1979_, 5, v_toBind_1974_);
    lean_closure_set(v___f_1979_, 6, v___f_1978_);
    v___x_1980_ = lean_apply_4(
        v_toBind_1974_,
        lean_box(0),
        lean_box(0),
        v_getRing_1975_,
        v___f_1979_,
    );
    return v___x_1980_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn(
    mut v_m_1981_: *mut LeanObject,
    mut v_inst_1982_: *mut LeanObject,
    mut v_inst_1983_: *mut LeanObject,
    mut v_inst_1984_: *mut LeanObject,
    mut v_inst_1985_: *mut LeanObject,
    mut v_inst_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_mulFn_1988_: *mut LeanObject,
    mut v_s_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_unused_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1990_ = lean_ctor_get(v_s_1989_, 0);
                v_type_1991_ = lean_ctor_get(v_s_1989_, 1);
                v_u_1992_ = lean_ctor_get(v_s_1989_, 2);
                v_ringInst_1993_ = lean_ctor_get(v_s_1989_, 3);
                v_semiringInst_1994_ = lean_ctor_get(v_s_1989_, 4);
                v_charInst_x3f_1995_ = lean_ctor_get(v_s_1989_, 5);
                v_addFn_x3f_1996_ = lean_ctor_get(v_s_1989_, 6);
                v_subFn_x3f_1997_ = lean_ctor_get(v_s_1989_, 8);
                v_negFn_x3f_1998_ = lean_ctor_get(v_s_1989_, 9);
                v_powFn_x3f_1999_ = lean_ctor_get(v_s_1989_, 10);
                v_intCastFn_x3f_2000_ = lean_ctor_get(v_s_1989_, 11);
                v_natCastFn_x3f_2001_ = lean_ctor_get(v_s_1989_, 12);
                v_one_x3f_2002_ = lean_ctor_get(v_s_1989_, 13);
                v_isSharedCheck_2010_ = (!lean_is_exclusive(v_s_1989_)) as u8;
                if v_isSharedCheck_2010_ == 0 {
                    v_unused_2011_ = lean_ctor_get(v_s_1989_, 7);
                    lean_dec(v_unused_2011_);
                    v___x_2004_ = v_s_1989_;
                    v_isShared_2005_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_one_x3f_2002_);
                    lean_inc(v_natCastFn_x3f_2001_);
                    lean_inc(v_intCastFn_x3f_2000_);
                    lean_inc(v_powFn_x3f_1999_);
                    lean_inc(v_negFn_x3f_1998_);
                    lean_inc(v_subFn_x3f_1997_);
                    lean_inc(v_addFn_x3f_1996_);
                    lean_inc(v_charInst_x3f_1995_);
                    lean_inc(v_semiringInst_1994_);
                    lean_inc(v_ringInst_1993_);
                    lean_inc(v_u_1992_);
                    lean_inc(v_type_1991_);
                    lean_inc(v_id_1990_);
                    lean_dec(v_s_1989_);
                    v___x_2004_ = lean_box(0);
                    v_isShared_2005_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2006_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2006_, 0, v_mulFn_1988_);
                if v_isShared_2005_ == 0 {
                    lean_ctor_set(v___x_2004_, 7, v___x_2006_);
                    v___x_2008_ = v___x_2004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 14, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_id_1990_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_type_1991_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_u_1992_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_ringInst_1993_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_semiringInst_1994_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 5, v_charInst_x3f_1995_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 6, v_addFn_x3f_1996_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 7, v___x_2006_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 8, v_subFn_x3f_1997_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 9, v_negFn_x3f_1998_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 10, v_powFn_x3f_1999_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 11, v_intCastFn_x3f_2000_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 12, v_natCastFn_x3f_2001_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 13, v_one_x3f_2002_);
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
    mut v_toPure_2012_: *mut LeanObject,
    mut v_mulFn_2013_: *mut LeanObject,
    mut v_____r_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = lean_apply_2(v_toPure_2012_, lean_box(0), v_mulFn_2013_);
    return v___x_2015_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(
    mut v_toPure_2016_: *mut LeanObject,
    mut v_modifyRing_2017_: *mut LeanObject,
    mut v_toBind_2018_: *mut LeanObject,
    mut v_mulFn_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_mulFn_2019_);
    v___f_2020_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2020_, 0, v_mulFn_2019_);
    v___f_2021_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2021_, 0, v_toPure_2016_);
    lean_closure_set(v___f_2021_, 1, v_mulFn_2019_);
    v___x_2022_ = lean_apply_1(v_modifyRing_2017_, v___f_2020_);
    v___x_2023_ = lean_apply_4(
        v_toBind_2018_,
        lean_box(0),
        lean_box(0),
        v___x_2022_,
        v___f_2021_,
    );
    return v___x_2023_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(
    mut v_toPure_2040_: *mut LeanObject,
    mut v_inst_2041_: *mut LeanObject,
    mut v_inst_2042_: *mut LeanObject,
    mut v_inst_2043_: *mut LeanObject,
    mut v_inst_2044_: *mut LeanObject,
    mut v_toBind_2045_: *mut LeanObject,
    mut v___f_2046_: *mut LeanObject,
    mut v_ring_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mulFn_x3f_2048_: *mut LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_2048_ = lean_ctor_get(v_ring_2047_, 7);
    if lean_obj_tag(v_mulFn_x3f_2048_) == 1 {
        let mut v_val_2049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_mulFn_x3f_2048_);
        lean_dec_ref(v_ring_2047_);
        lean_dec(v___f_2046_);
        lean_dec(v_toBind_2045_);
        lean_dec_ref(v_inst_2044_);
        lean_dec_ref(v_inst_2043_);
        lean_dec_ref(v_inst_2042_);
        lean_dec(v_inst_2041_);
        v_val_2049_ = lean_ctor_get(v_mulFn_x3f_2048_, 0);
        lean_inc(v_val_2049_);
        lean_dec_ref_known(v_mulFn_x3f_2048_, 1);
        v___x_2050_ = lean_apply_2(v_toPure_2040_, lean_box(0), v_val_2049_);
        return v___x_2050_;
    } else {
        let mut v_type_2051_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2052_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2040_);
        v_type_2051_ = lean_ctor_get(v_ring_2047_, 1);
        lean_inc_ref_n(v_type_2051_, 3);
        v_u_2052_ = lean_ctor_get(v_ring_2047_, 2);
        lean_inc_n(v_u_2052_, 2);
        v_semiringInst_2053_ = lean_ctor_get(v_ring_2047_, 4);
        lean_inc_ref(v_semiringInst_2053_);
        lean_dec_ref(v_ring_2047_);
        v___x_2054_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1;
        v___x_2055_ = lean_box(0);
        v___x_2056_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2056_, 0, v_u_2052_);
        lean_ctor_set(v___x_2056_, 1, v___x_2055_);
        lean_inc_ref(v___x_2056_);
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
        v___x_2065_ = lean_apply_4(
            v_toBind_2045_,
            lean_box(0),
            lean_box(0),
            v___x_2064_,
            v___f_2046_,
        );
        return v___x_2065_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn___redArg(
    mut v_inst_2066_: *mut LeanObject,
    mut v_inst_2067_: *mut LeanObject,
    mut v_inst_2068_: *mut LeanObject,
    mut v_inst_2069_: *mut LeanObject,
    mut v_inst_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2071_ = lean_ctor_get(v_inst_2068_, 0);
    v_toBind_2072_ = lean_ctor_get(v_inst_2068_, 1);
    lean_inc_n(v_toBind_2072_, 3);
    v_getRing_2073_ = lean_ctor_get(v_inst_2070_, 0);
    lean_inc(v_getRing_2073_);
    v_modifyRing_2074_ = lean_ctor_get(v_inst_2070_, 1);
    lean_inc(v_modifyRing_2074_);
    lean_dec_ref(v_inst_2070_);
    v_toPure_2075_ = lean_ctor_get(v_toApplicative_2071_, 1);
    lean_inc_n(v_toPure_2075_, 2);
    v___f_2076_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2076_, 0, v_toPure_2075_);
    lean_closure_set(v___f_2076_, 1, v_modifyRing_2074_);
    lean_closure_set(v___f_2076_, 2, v_toBind_2072_);
    v___f_2077_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2077_, 0, v_toPure_2075_);
    lean_closure_set(v___f_2077_, 1, v_inst_2066_);
    lean_closure_set(v___f_2077_, 2, v_inst_2067_);
    lean_closure_set(v___f_2077_, 3, v_inst_2068_);
    lean_closure_set(v___f_2077_, 4, v_inst_2069_);
    lean_closure_set(v___f_2077_, 5, v_toBind_2072_);
    lean_closure_set(v___f_2077_, 6, v___f_2076_);
    v___x_2078_ = lean_apply_4(
        v_toBind_2072_,
        lean_box(0),
        lean_box(0),
        v_getRing_2073_,
        v___f_2077_,
    );
    return v___x_2078_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn(
    mut v_m_2079_: *mut LeanObject,
    mut v_inst_2080_: *mut LeanObject,
    mut v_inst_2081_: *mut LeanObject,
    mut v_inst_2082_: *mut LeanObject,
    mut v_inst_2083_: *mut LeanObject,
    mut v_inst_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_subFn_2086_: *mut LeanObject,
    mut v_s_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_unused_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2088_ = lean_ctor_get(v_s_2087_, 0);
                v_type_2089_ = lean_ctor_get(v_s_2087_, 1);
                v_u_2090_ = lean_ctor_get(v_s_2087_, 2);
                v_ringInst_2091_ = lean_ctor_get(v_s_2087_, 3);
                v_semiringInst_2092_ = lean_ctor_get(v_s_2087_, 4);
                v_charInst_x3f_2093_ = lean_ctor_get(v_s_2087_, 5);
                v_addFn_x3f_2094_ = lean_ctor_get(v_s_2087_, 6);
                v_mulFn_x3f_2095_ = lean_ctor_get(v_s_2087_, 7);
                v_negFn_x3f_2096_ = lean_ctor_get(v_s_2087_, 9);
                v_powFn_x3f_2097_ = lean_ctor_get(v_s_2087_, 10);
                v_intCastFn_x3f_2098_ = lean_ctor_get(v_s_2087_, 11);
                v_natCastFn_x3f_2099_ = lean_ctor_get(v_s_2087_, 12);
                v_one_x3f_2100_ = lean_ctor_get(v_s_2087_, 13);
                v_isSharedCheck_2108_ = (!lean_is_exclusive(v_s_2087_)) as u8;
                if v_isSharedCheck_2108_ == 0 {
                    v_unused_2109_ = lean_ctor_get(v_s_2087_, 8);
                    lean_dec(v_unused_2109_);
                    v___x_2102_ = v_s_2087_;
                    v_isShared_2103_ = v_isSharedCheck_2108_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_one_x3f_2100_);
                    lean_inc(v_natCastFn_x3f_2099_);
                    lean_inc(v_intCastFn_x3f_2098_);
                    lean_inc(v_powFn_x3f_2097_);
                    lean_inc(v_negFn_x3f_2096_);
                    lean_inc(v_mulFn_x3f_2095_);
                    lean_inc(v_addFn_x3f_2094_);
                    lean_inc(v_charInst_x3f_2093_);
                    lean_inc(v_semiringInst_2092_);
                    lean_inc(v_ringInst_2091_);
                    lean_inc(v_u_2090_);
                    lean_inc(v_type_2089_);
                    lean_inc(v_id_2088_);
                    lean_dec(v_s_2087_);
                    v___x_2102_ = lean_box(0);
                    v_isShared_2103_ = v_isSharedCheck_2108_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2104_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2104_, 0, v_subFn_2086_);
                if v_isShared_2103_ == 0 {
                    lean_ctor_set(v___x_2102_, 8, v___x_2104_);
                    v___x_2106_ = v___x_2102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 14, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_id_2088_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_type_2089_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_u_2090_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_ringInst_2091_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 4, v_semiringInst_2092_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 5, v_charInst_x3f_2093_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 6, v_addFn_x3f_2094_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 7, v_mulFn_x3f_2095_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 8, v___x_2104_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 9, v_negFn_x3f_2096_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 10, v_powFn_x3f_2097_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 11, v_intCastFn_x3f_2098_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 12, v_natCastFn_x3f_2099_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 13, v_one_x3f_2100_);
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
    mut v_toPure_2110_: *mut LeanObject,
    mut v_subFn_2111_: *mut LeanObject,
    mut v_____r_2112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    v___x_2113_ = lean_apply_2(v_toPure_2110_, lean_box(0), v_subFn_2111_);
    return v___x_2113_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(
    mut v_toPure_2114_: *mut LeanObject,
    mut v_modifyRing_2115_: *mut LeanObject,
    mut v_toBind_2116_: *mut LeanObject,
    mut v_subFn_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_subFn_2117_);
    v___f_2118_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2118_, 0, v_subFn_2117_);
    v___f_2119_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2119_, 0, v_toPure_2114_);
    lean_closure_set(v___f_2119_, 1, v_subFn_2117_);
    v___x_2120_ = lean_apply_1(v_modifyRing_2115_, v___f_2118_);
    v___x_2121_ = lean_apply_4(
        v_toBind_2116_,
        lean_box(0),
        lean_box(0),
        v___x_2120_,
        v___f_2119_,
    );
    return v___x_2121_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(
    mut v_toPure_2139_: *mut LeanObject,
    mut v_inst_2140_: *mut LeanObject,
    mut v_inst_2141_: *mut LeanObject,
    mut v_inst_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_toBind_2144_: *mut LeanObject,
    mut v___f_2145_: *mut LeanObject,
    mut v_ring_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subFn_x3f_2147_: *mut LeanObject = core::ptr::null_mut();
    v_subFn_x3f_2147_ = lean_ctor_get(v_ring_2146_, 8);
    if lean_obj_tag(v_subFn_x3f_2147_) == 1 {
        let mut v_val_2148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_subFn_x3f_2147_);
        lean_dec_ref(v_ring_2146_);
        lean_dec(v___f_2145_);
        lean_dec(v_toBind_2144_);
        lean_dec_ref(v_inst_2143_);
        lean_dec_ref(v_inst_2142_);
        lean_dec_ref(v_inst_2141_);
        lean_dec(v_inst_2140_);
        v_val_2148_ = lean_ctor_get(v_subFn_x3f_2147_, 0);
        lean_inc(v_val_2148_);
        lean_dec_ref_known(v_subFn_x3f_2147_, 1);
        v___x_2149_ = lean_apply_2(v_toPure_2139_, lean_box(0), v_val_2148_);
        return v___x_2149_;
    } else {
        let mut v_type_2150_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2151_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ringInst_2152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2139_);
        v_type_2150_ = lean_ctor_get(v_ring_2146_, 1);
        lean_inc_ref_n(v_type_2150_, 3);
        v_u_2151_ = lean_ctor_get(v_ring_2146_, 2);
        lean_inc_n(v_u_2151_, 2);
        v_ringInst_2152_ = lean_ctor_get(v_ring_2146_, 3);
        lean_inc_ref(v_ringInst_2152_);
        lean_dec_ref(v_ring_2146_);
        v___x_2153_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1;
        v___x_2154_ = lean_box(0);
        v___x_2155_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2155_, 0, v_u_2151_);
        lean_ctor_set(v___x_2155_, 1, v___x_2154_);
        lean_inc_ref(v___x_2155_);
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
        v___x_2164_ = lean_apply_4(
            v_toBind_2144_,
            lean_box(0),
            lean_box(0),
            v___x_2163_,
            v___f_2145_,
        );
        return v___x_2164_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn___redArg(
    mut v_inst_2165_: *mut LeanObject,
    mut v_inst_2166_: *mut LeanObject,
    mut v_inst_2167_: *mut LeanObject,
    mut v_inst_2168_: *mut LeanObject,
    mut v_inst_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2170_ = lean_ctor_get(v_inst_2167_, 0);
    v_toBind_2171_ = lean_ctor_get(v_inst_2167_, 1);
    lean_inc_n(v_toBind_2171_, 3);
    v_getRing_2172_ = lean_ctor_get(v_inst_2169_, 0);
    lean_inc(v_getRing_2172_);
    v_modifyRing_2173_ = lean_ctor_get(v_inst_2169_, 1);
    lean_inc(v_modifyRing_2173_);
    lean_dec_ref(v_inst_2169_);
    v_toPure_2174_ = lean_ctor_get(v_toApplicative_2170_, 1);
    lean_inc_n(v_toPure_2174_, 2);
    v___f_2175_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2175_, 0, v_toPure_2174_);
    lean_closure_set(v___f_2175_, 1, v_modifyRing_2173_);
    lean_closure_set(v___f_2175_, 2, v_toBind_2171_);
    v___f_2176_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2176_, 0, v_toPure_2174_);
    lean_closure_set(v___f_2176_, 1, v_inst_2165_);
    lean_closure_set(v___f_2176_, 2, v_inst_2166_);
    lean_closure_set(v___f_2176_, 3, v_inst_2167_);
    lean_closure_set(v___f_2176_, 4, v_inst_2168_);
    lean_closure_set(v___f_2176_, 5, v_toBind_2171_);
    lean_closure_set(v___f_2176_, 6, v___f_2175_);
    v___x_2177_ = lean_apply_4(
        v_toBind_2171_,
        lean_box(0),
        lean_box(0),
        v_getRing_2172_,
        v___f_2176_,
    );
    return v___x_2177_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getSubFn(
    mut v_m_2178_: *mut LeanObject,
    mut v_inst_2179_: *mut LeanObject,
    mut v_inst_2180_: *mut LeanObject,
    mut v_inst_2181_: *mut LeanObject,
    mut v_inst_2182_: *mut LeanObject,
    mut v_inst_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_negFn_2185_: *mut LeanObject,
    mut v_s_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_unused_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2187_ = lean_ctor_get(v_s_2186_, 0);
                v_type_2188_ = lean_ctor_get(v_s_2186_, 1);
                v_u_2189_ = lean_ctor_get(v_s_2186_, 2);
                v_ringInst_2190_ = lean_ctor_get(v_s_2186_, 3);
                v_semiringInst_2191_ = lean_ctor_get(v_s_2186_, 4);
                v_charInst_x3f_2192_ = lean_ctor_get(v_s_2186_, 5);
                v_addFn_x3f_2193_ = lean_ctor_get(v_s_2186_, 6);
                v_mulFn_x3f_2194_ = lean_ctor_get(v_s_2186_, 7);
                v_subFn_x3f_2195_ = lean_ctor_get(v_s_2186_, 8);
                v_powFn_x3f_2196_ = lean_ctor_get(v_s_2186_, 10);
                v_intCastFn_x3f_2197_ = lean_ctor_get(v_s_2186_, 11);
                v_natCastFn_x3f_2198_ = lean_ctor_get(v_s_2186_, 12);
                v_one_x3f_2199_ = lean_ctor_get(v_s_2186_, 13);
                v_isSharedCheck_2207_ = (!lean_is_exclusive(v_s_2186_)) as u8;
                if v_isSharedCheck_2207_ == 0 {
                    v_unused_2208_ = lean_ctor_get(v_s_2186_, 9);
                    lean_dec(v_unused_2208_);
                    v___x_2201_ = v_s_2186_;
                    v_isShared_2202_ = v_isSharedCheck_2207_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_one_x3f_2199_);
                    lean_inc(v_natCastFn_x3f_2198_);
                    lean_inc(v_intCastFn_x3f_2197_);
                    lean_inc(v_powFn_x3f_2196_);
                    lean_inc(v_subFn_x3f_2195_);
                    lean_inc(v_mulFn_x3f_2194_);
                    lean_inc(v_addFn_x3f_2193_);
                    lean_inc(v_charInst_x3f_2192_);
                    lean_inc(v_semiringInst_2191_);
                    lean_inc(v_ringInst_2190_);
                    lean_inc(v_u_2189_);
                    lean_inc(v_type_2188_);
                    lean_inc(v_id_2187_);
                    lean_dec(v_s_2186_);
                    v___x_2201_ = lean_box(0);
                    v_isShared_2202_ = v_isSharedCheck_2207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2203_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2203_, 0, v_negFn_2185_);
                if v_isShared_2202_ == 0 {
                    lean_ctor_set(v___x_2201_, 9, v___x_2203_);
                    v___x_2205_ = v___x_2201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 14, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_id_2187_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_type_2188_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_u_2189_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_ringInst_2190_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_semiringInst_2191_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 5, v_charInst_x3f_2192_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 6, v_addFn_x3f_2193_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 7, v_mulFn_x3f_2194_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 8, v_subFn_x3f_2195_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 9, v___x_2203_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 10, v_powFn_x3f_2196_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 11, v_intCastFn_x3f_2197_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 12, v_natCastFn_x3f_2198_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 13, v_one_x3f_2199_);
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
    mut v_toPure_2209_: *mut LeanObject,
    mut v_negFn_2210_: *mut LeanObject,
    mut v_____r_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    v___x_2212_ = lean_apply_2(v_toPure_2209_, lean_box(0), v_negFn_2210_);
    return v___x_2212_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(
    mut v_toPure_2213_: *mut LeanObject,
    mut v_modifyRing_2214_: *mut LeanObject,
    mut v_toBind_2215_: *mut LeanObject,
    mut v_negFn_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_negFn_2216_);
    v___f_2217_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2217_, 0, v_negFn_2216_);
    v___f_2218_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2218_, 0, v_toPure_2213_);
    lean_closure_set(v___f_2218_, 1, v_negFn_2216_);
    v___x_2219_ = lean_apply_1(v_modifyRing_2214_, v___f_2217_);
    v___x_2220_ = lean_apply_4(
        v_toBind_2215_,
        lean_box(0),
        lean_box(0),
        v___x_2219_,
        v___f_2218_,
    );
    return v___x_2220_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(
    mut v_toPure_2234_: *mut LeanObject,
    mut v_inst_2235_: *mut LeanObject,
    mut v_inst_2236_: *mut LeanObject,
    mut v_inst_2237_: *mut LeanObject,
    mut v_inst_2238_: *mut LeanObject,
    mut v_toBind_2239_: *mut LeanObject,
    mut v___f_2240_: *mut LeanObject,
    mut v_ring_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_negFn_x3f_2242_: *mut LeanObject = core::ptr::null_mut();
    v_negFn_x3f_2242_ = lean_ctor_get(v_ring_2241_, 9);
    if lean_obj_tag(v_negFn_x3f_2242_) == 1 {
        let mut v_val_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_negFn_x3f_2242_);
        lean_dec_ref(v_ring_2241_);
        lean_dec(v___f_2240_);
        lean_dec(v_toBind_2239_);
        lean_dec_ref(v_inst_2238_);
        lean_dec_ref(v_inst_2237_);
        lean_dec_ref(v_inst_2236_);
        lean_dec(v_inst_2235_);
        v_val_2243_ = lean_ctor_get(v_negFn_x3f_2242_, 0);
        lean_inc(v_val_2243_);
        lean_dec_ref_known(v_negFn_x3f_2242_, 1);
        v___x_2244_ = lean_apply_2(v_toPure_2234_, lean_box(0), v_val_2243_);
        return v___x_2244_;
    } else {
        let mut v_type_2245_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2246_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ringInst_2247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2234_);
        v_type_2245_ = lean_ctor_get(v_ring_2241_, 1);
        lean_inc_ref_n(v_type_2245_, 2);
        v_u_2246_ = lean_ctor_get(v_ring_2241_, 2);
        lean_inc_n(v_u_2246_, 2);
        v_ringInst_2247_ = lean_ctor_get(v_ring_2241_, 3);
        lean_inc_ref(v_ringInst_2247_);
        lean_dec_ref(v_ring_2241_);
        v___x_2248_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1;
        v___x_2249_ = lean_box(0);
        v___x_2250_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2250_, 0, v_u_2246_);
        lean_ctor_set(v___x_2250_, 1, v___x_2249_);
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
        v___x_2256_ = lean_apply_4(
            v_toBind_2239_,
            lean_box(0),
            lean_box(0),
            v___x_2255_,
            v___f_2240_,
        );
        return v___x_2256_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn___redArg(
    mut v_inst_2257_: *mut LeanObject,
    mut v_inst_2258_: *mut LeanObject,
    mut v_inst_2259_: *mut LeanObject,
    mut v_inst_2260_: *mut LeanObject,
    mut v_inst_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2262_ = lean_ctor_get(v_inst_2259_, 0);
    v_toBind_2263_ = lean_ctor_get(v_inst_2259_, 1);
    lean_inc_n(v_toBind_2263_, 3);
    v_getRing_2264_ = lean_ctor_get(v_inst_2261_, 0);
    lean_inc(v_getRing_2264_);
    v_modifyRing_2265_ = lean_ctor_get(v_inst_2261_, 1);
    lean_inc(v_modifyRing_2265_);
    lean_dec_ref(v_inst_2261_);
    v_toPure_2266_ = lean_ctor_get(v_toApplicative_2262_, 1);
    lean_inc_n(v_toPure_2266_, 2);
    v___f_2267_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2267_, 0, v_toPure_2266_);
    lean_closure_set(v___f_2267_, 1, v_modifyRing_2265_);
    lean_closure_set(v___f_2267_, 2, v_toBind_2263_);
    v___f_2268_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2268_, 0, v_toPure_2266_);
    lean_closure_set(v___f_2268_, 1, v_inst_2257_);
    lean_closure_set(v___f_2268_, 2, v_inst_2258_);
    lean_closure_set(v___f_2268_, 3, v_inst_2259_);
    lean_closure_set(v___f_2268_, 4, v_inst_2260_);
    lean_closure_set(v___f_2268_, 5, v_toBind_2263_);
    lean_closure_set(v___f_2268_, 6, v___f_2267_);
    v___x_2269_ = lean_apply_4(
        v_toBind_2263_,
        lean_box(0),
        lean_box(0),
        v_getRing_2264_,
        v___f_2268_,
    );
    return v___x_2269_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNegFn(
    mut v_m_2270_: *mut LeanObject,
    mut v_inst_2271_: *mut LeanObject,
    mut v_inst_2272_: *mut LeanObject,
    mut v_inst_2273_: *mut LeanObject,
    mut v_inst_2274_: *mut LeanObject,
    mut v_inst_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_powFn_2277_: *mut LeanObject,
    mut v_s_2278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2279_ = lean_ctor_get(v_s_2278_, 0);
                v_type_2280_ = lean_ctor_get(v_s_2278_, 1);
                v_u_2281_ = lean_ctor_get(v_s_2278_, 2);
                v_ringInst_2282_ = lean_ctor_get(v_s_2278_, 3);
                v_semiringInst_2283_ = lean_ctor_get(v_s_2278_, 4);
                v_charInst_x3f_2284_ = lean_ctor_get(v_s_2278_, 5);
                v_addFn_x3f_2285_ = lean_ctor_get(v_s_2278_, 6);
                v_mulFn_x3f_2286_ = lean_ctor_get(v_s_2278_, 7);
                v_subFn_x3f_2287_ = lean_ctor_get(v_s_2278_, 8);
                v_negFn_x3f_2288_ = lean_ctor_get(v_s_2278_, 9);
                v_intCastFn_x3f_2289_ = lean_ctor_get(v_s_2278_, 11);
                v_natCastFn_x3f_2290_ = lean_ctor_get(v_s_2278_, 12);
                v_one_x3f_2291_ = lean_ctor_get(v_s_2278_, 13);
                v_isSharedCheck_2299_ = (!lean_is_exclusive(v_s_2278_)) as u8;
                if v_isSharedCheck_2299_ == 0 {
                    v_unused_2300_ = lean_ctor_get(v_s_2278_, 10);
                    lean_dec(v_unused_2300_);
                    v___x_2293_ = v_s_2278_;
                    v_isShared_2294_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_one_x3f_2291_);
                    lean_inc(v_natCastFn_x3f_2290_);
                    lean_inc(v_intCastFn_x3f_2289_);
                    lean_inc(v_negFn_x3f_2288_);
                    lean_inc(v_subFn_x3f_2287_);
                    lean_inc(v_mulFn_x3f_2286_);
                    lean_inc(v_addFn_x3f_2285_);
                    lean_inc(v_charInst_x3f_2284_);
                    lean_inc(v_semiringInst_2283_);
                    lean_inc(v_ringInst_2282_);
                    lean_inc(v_u_2281_);
                    lean_inc(v_type_2280_);
                    lean_inc(v_id_2279_);
                    lean_dec(v_s_2278_);
                    v___x_2293_ = lean_box(0);
                    v_isShared_2294_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2295_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2295_, 0, v_powFn_2277_);
                if v_isShared_2294_ == 0 {
                    lean_ctor_set(v___x_2293_, 10, v___x_2295_);
                    v___x_2297_ = v___x_2293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 14, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_id_2279_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_type_2280_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_u_2281_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 3, v_ringInst_2282_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 4, v_semiringInst_2283_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 5, v_charInst_x3f_2284_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 6, v_addFn_x3f_2285_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 7, v_mulFn_x3f_2286_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 8, v_subFn_x3f_2287_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 9, v_negFn_x3f_2288_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 10, v___x_2295_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 11, v_intCastFn_x3f_2289_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 12, v_natCastFn_x3f_2290_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 13, v_one_x3f_2291_);
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
    mut v_toPure_2301_: *mut LeanObject,
    mut v_powFn_2302_: *mut LeanObject,
    mut v_____r_2303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ = lean_apply_2(v_toPure_2301_, lean_box(0), v_powFn_2302_);
    return v___x_2304_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(
    mut v_toPure_2305_: *mut LeanObject,
    mut v_modifyRing_2306_: *mut LeanObject,
    mut v_toBind_2307_: *mut LeanObject,
    mut v_powFn_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_powFn_2308_);
    v___f_2309_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2309_, 0, v_powFn_2308_);
    v___f_2310_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2310_, 0, v_toPure_2305_);
    lean_closure_set(v___f_2310_, 1, v_powFn_2308_);
    v___x_2311_ = lean_apply_1(v_modifyRing_2306_, v___f_2309_);
    v___x_2312_ = lean_apply_4(
        v_toBind_2307_,
        lean_box(0),
        lean_box(0),
        v___x_2311_,
        v___f_2310_,
    );
    return v___x_2312_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(
    mut v_toPure_2313_: *mut LeanObject,
    mut v_inst_2314_: *mut LeanObject,
    mut v_inst_2315_: *mut LeanObject,
    mut v_inst_2316_: *mut LeanObject,
    mut v_inst_2317_: *mut LeanObject,
    mut v_toBind_2318_: *mut LeanObject,
    mut v___f_2319_: *mut LeanObject,
    mut v_ring_2320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_powFn_x3f_2321_: *mut LeanObject = core::ptr::null_mut();
    v_powFn_x3f_2321_ = lean_ctor_get(v_ring_2320_, 10);
    if lean_obj_tag(v_powFn_x3f_2321_) == 1 {
        let mut v_val_2322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_powFn_x3f_2321_);
        lean_dec_ref(v_ring_2320_);
        lean_dec(v___f_2319_);
        lean_dec(v_toBind_2318_);
        lean_dec_ref(v_inst_2317_);
        lean_dec_ref(v_inst_2316_);
        lean_dec_ref(v_inst_2315_);
        lean_dec(v_inst_2314_);
        v_val_2322_ = lean_ctor_get(v_powFn_x3f_2321_, 0);
        lean_inc(v_val_2322_);
        lean_dec_ref_known(v_powFn_x3f_2321_, 1);
        v___x_2323_ = lean_apply_2(v_toPure_2313_, lean_box(0), v_val_2322_);
        return v___x_2323_;
    } else {
        let mut v_type_2324_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2325_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2313_);
        v_type_2324_ = lean_ctor_get(v_ring_2320_, 1);
        lean_inc_ref(v_type_2324_);
        v_u_2325_ = lean_ctor_get(v_ring_2320_, 2);
        lean_inc(v_u_2325_);
        v_semiringInst_2326_ = lean_ctor_get(v_ring_2320_, 4);
        lean_inc_ref(v_semiringInst_2326_);
        lean_dec_ref(v_ring_2320_);
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
        v___x_2328_ = lean_apply_4(
            v_toBind_2318_,
            lean_box(0),
            lean_box(0),
            v___x_2327_,
            v___f_2319_,
        );
        return v___x_2328_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn___redArg(
    mut v_inst_2329_: *mut LeanObject,
    mut v_inst_2330_: *mut LeanObject,
    mut v_inst_2331_: *mut LeanObject,
    mut v_inst_2332_: *mut LeanObject,
    mut v_inst_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2334_ = lean_ctor_get(v_inst_2331_, 0);
    v_toBind_2335_ = lean_ctor_get(v_inst_2331_, 1);
    lean_inc_n(v_toBind_2335_, 3);
    v_getRing_2336_ = lean_ctor_get(v_inst_2333_, 0);
    lean_inc(v_getRing_2336_);
    v_modifyRing_2337_ = lean_ctor_get(v_inst_2333_, 1);
    lean_inc(v_modifyRing_2337_);
    lean_dec_ref(v_inst_2333_);
    v_toPure_2338_ = lean_ctor_get(v_toApplicative_2334_, 1);
    lean_inc_n(v_toPure_2338_, 2);
    v___f_2339_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2339_, 0, v_toPure_2338_);
    lean_closure_set(v___f_2339_, 1, v_modifyRing_2337_);
    lean_closure_set(v___f_2339_, 2, v_toBind_2335_);
    v___f_2340_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2340_, 0, v_toPure_2338_);
    lean_closure_set(v___f_2340_, 1, v_inst_2329_);
    lean_closure_set(v___f_2340_, 2, v_inst_2330_);
    lean_closure_set(v___f_2340_, 3, v_inst_2331_);
    lean_closure_set(v___f_2340_, 4, v_inst_2332_);
    lean_closure_set(v___f_2340_, 5, v_toBind_2335_);
    lean_closure_set(v___f_2340_, 6, v___f_2339_);
    v___x_2341_ = lean_apply_4(
        v_toBind_2335_,
        lean_box(0),
        lean_box(0),
        v_getRing_2336_,
        v___f_2340_,
    );
    return v___x_2341_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn(
    mut v_m_2342_: *mut LeanObject,
    mut v_inst_2343_: *mut LeanObject,
    mut v_inst_2344_: *mut LeanObject,
    mut v_inst_2345_: *mut LeanObject,
    mut v_inst_2346_: *mut LeanObject,
    mut v_inst_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_intCastFn_2349_: *mut LeanObject,
    mut v_s_2350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_unused_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2351_ = lean_ctor_get(v_s_2350_, 0);
                v_type_2352_ = lean_ctor_get(v_s_2350_, 1);
                v_u_2353_ = lean_ctor_get(v_s_2350_, 2);
                v_ringInst_2354_ = lean_ctor_get(v_s_2350_, 3);
                v_semiringInst_2355_ = lean_ctor_get(v_s_2350_, 4);
                v_charInst_x3f_2356_ = lean_ctor_get(v_s_2350_, 5);
                v_addFn_x3f_2357_ = lean_ctor_get(v_s_2350_, 6);
                v_mulFn_x3f_2358_ = lean_ctor_get(v_s_2350_, 7);
                v_subFn_x3f_2359_ = lean_ctor_get(v_s_2350_, 8);
                v_negFn_x3f_2360_ = lean_ctor_get(v_s_2350_, 9);
                v_powFn_x3f_2361_ = lean_ctor_get(v_s_2350_, 10);
                v_natCastFn_x3f_2362_ = lean_ctor_get(v_s_2350_, 12);
                v_one_x3f_2363_ = lean_ctor_get(v_s_2350_, 13);
                v_isSharedCheck_2371_ = (!lean_is_exclusive(v_s_2350_)) as u8;
                if v_isSharedCheck_2371_ == 0 {
                    v_unused_2372_ = lean_ctor_get(v_s_2350_, 11);
                    lean_dec(v_unused_2372_);
                    v___x_2365_ = v_s_2350_;
                    v_isShared_2366_ = v_isSharedCheck_2371_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_one_x3f_2363_);
                    lean_inc(v_natCastFn_x3f_2362_);
                    lean_inc(v_powFn_x3f_2361_);
                    lean_inc(v_negFn_x3f_2360_);
                    lean_inc(v_subFn_x3f_2359_);
                    lean_inc(v_mulFn_x3f_2358_);
                    lean_inc(v_addFn_x3f_2357_);
                    lean_inc(v_charInst_x3f_2356_);
                    lean_inc(v_semiringInst_2355_);
                    lean_inc(v_ringInst_2354_);
                    lean_inc(v_u_2353_);
                    lean_inc(v_type_2352_);
                    lean_inc(v_id_2351_);
                    lean_dec(v_s_2350_);
                    v___x_2365_ = lean_box(0);
                    v_isShared_2366_ = v_isSharedCheck_2371_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2367_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2367_, 0, v_intCastFn_2349_);
                if v_isShared_2366_ == 0 {
                    lean_ctor_set(v___x_2365_, 11, v___x_2367_);
                    v___x_2369_ = v___x_2365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 14, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_id_2351_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_type_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_u_2353_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_ringInst_2354_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_semiringInst_2355_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 5, v_charInst_x3f_2356_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 6, v_addFn_x3f_2357_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 7, v_mulFn_x3f_2358_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 8, v_subFn_x3f_2359_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 9, v_negFn_x3f_2360_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 10, v_powFn_x3f_2361_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 11, v___x_2367_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 12, v_natCastFn_x3f_2362_);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 13, v_one_x3f_2363_);
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
    mut v_toPure_2373_: *mut LeanObject,
    mut v_intCastFn_2374_: *mut LeanObject,
    mut v_____r_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2376_ = lean_apply_2(v_toPure_2373_, lean_box(0), v_intCastFn_2374_);
    return v___x_2376_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(
    mut v_toPure_2377_: *mut LeanObject,
    mut v_modifyRing_2378_: *mut LeanObject,
    mut v_toBind_2379_: *mut LeanObject,
    mut v_intCastFn_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_intCastFn_2380_);
    v___f_2381_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2381_, 0, v_intCastFn_2380_);
    v___f_2382_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2382_, 0, v_toPure_2377_);
    lean_closure_set(v___f_2382_, 1, v_intCastFn_2380_);
    v___x_2383_ = lean_apply_1(v_modifyRing_2378_, v___f_2381_);
    v___x_2384_ = lean_apply_4(
        v_toBind_2379_,
        lean_box(0),
        lean_box(0),
        v___x_2383_,
        v___f_2382_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(
    mut v___x_2385_: *mut LeanObject,
    mut v___x_2386_: *mut LeanObject,
    mut v___x_2387_: *mut LeanObject,
    mut v_type_2388_: *mut LeanObject,
    mut v_canonExpr_2389_: *mut LeanObject,
    mut v_toBind_2390_: *mut LeanObject,
    mut v___f_2391_: *mut LeanObject,
    mut v_inst_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Lean_Name_mkStr2(v___x_2385_, v___x_2386_);
    v___x_2394_ = l_Lean_mkConst(v___x_2393_, v___x_2387_);
    v___x_2395_ = l_Lean_mkAppB(v___x_2394_, v_type_2388_, v_inst_2392_);
    v___x_2396_ = lean_apply_1(v_canonExpr_2389_, v___x_2395_);
    v___x_2397_ = lean_apply_4(
        v_toBind_2390_,
        lean_box(0),
        lean_box(0),
        v___x_2396_,
        v___f_2391_,
    );
    return v___x_2397_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(
    mut v_toPure_2403_: *mut LeanObject,
    mut v_inst_x27_2404_: *mut LeanObject,
    mut v_toBind_2405_: *mut LeanObject,
    mut v___f_2406_: *mut LeanObject,
    mut v___f_2407_: *mut LeanObject,
    mut v_inst_2408_: *mut LeanObject,
    mut v_____do__lift_2409_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2409_) == 0 {
        let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_2408_);
        lean_dec(v___f_2407_);
        v___x_2410_ = lean_apply_2(v_toPure_2403_, lean_box(0), v_inst_x27_2404_);
        v___x_2411_ = lean_apply_4(
            v_toBind_2405_,
            lean_box(0),
            lean_box(0),
            v___x_2410_,
            v___f_2406_,
        );
        return v___x_2411_;
    } else {
        let mut v_val_2412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2406_);
        v_val_2412_ = lean_ctor_get(v_____do__lift_2409_, 0);
        lean_inc_n(v_val_2412_, 2);
        lean_dec_ref_known(v_____do__lift_2409_, 1);
        lean_inc(v_toBind_2405_);
        v___f_2413_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___f_2413_, 0, v_toPure_2403_);
        lean_closure_set(v___f_2413_, 1, v_val_2412_);
        lean_closure_set(v___f_2413_, 2, v_toBind_2405_);
        lean_closure_set(v___f_2413_, 3, v___f_2407_);
        v___x_2414_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2;
        v___x_2415_ = lean_alloc_closure(
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed
                as *mut core::ffi::c_void,
            8,
            3,
        );
        lean_closure_set(v___x_2415_, 0, v___x_2414_);
        lean_closure_set(v___x_2415_, 1, v_val_2412_);
        lean_closure_set(v___x_2415_, 2, v_inst_x27_2404_);
        v___x_2416_ = lean_apply_2(v_inst_2408_, lean_box(0), v___x_2415_);
        v___x_2417_ = lean_apply_4(
            v_toBind_2405_,
            lean_box(0),
            lean_box(0),
            v___x_2416_,
            v___f_2413_,
        );
        return v___x_2417_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(
    mut v_toPure_2427_: *mut LeanObject,
    mut v_inst_2428_: *mut LeanObject,
    mut v_toBind_2429_: *mut LeanObject,
    mut v___f_2430_: *mut LeanObject,
    mut v_inst_2431_: *mut LeanObject,
    mut v_ring_2432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intCastFn_x3f_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instType_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_intCastFn_x3f_2433_ = lean_ctor_get(v_ring_2432_, 11);
                if lean_obj_tag(v_intCastFn_x3f_2433_) == 1 {
                    lean_inc_ref(v_intCastFn_x3f_2433_);
                    lean_dec_ref(v_ring_2432_);
                    lean_dec(v_inst_2431_);
                    lean_dec(v___f_2430_);
                    lean_dec(v_toBind_2429_);
                    lean_dec_ref(v_inst_2428_);
                    v_val_2434_ = lean_ctor_get(v_intCastFn_x3f_2433_, 0);
                    lean_inc(v_val_2434_);
                    lean_dec_ref_known(v_intCastFn_x3f_2433_, 1);
                    v___x_2435_ = lean_apply_2(v_toPure_2427_, lean_box(0), v_val_2434_);
                    return v___x_2435_;
                } else {
                    v_type_2436_ = lean_ctor_get(v_ring_2432_, 1);
                    lean_inc_ref(v_type_2436_);
                    v_u_2437_ = lean_ctor_get(v_ring_2432_, 2);
                    lean_inc(v_u_2437_);
                    v_ringInst_2438_ = lean_ctor_get(v_ring_2432_, 3);
                    lean_inc_ref(v_ringInst_2438_);
                    lean_dec_ref(v_ring_2432_);
                    v_canonExpr_2439_ = lean_ctor_get(v_inst_2428_, 0);
                    v_synthInstance_x3f_2440_ = lean_ctor_get(v_inst_2428_, 1);
                    v_isSharedCheck_2461_ = (!lean_is_exclusive(v_inst_2428_)) as u8;
                    if v_isSharedCheck_2461_ == 0 {
                        v___x_2442_ = v_inst_2428_;
                        v_isShared_2443_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_synthInstance_x3f_2440_);
                        lean_inc(v_canonExpr_2439_);
                        lean_dec(v_inst_2428_);
                        v___x_2442_ = lean_box(0);
                        v_isShared_2443_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2444_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0;
                v___x_2445_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1;
                v___x_2446_ = lean_box(0);
                if v_isShared_2443_ == 0 {
                    lean_ctor_set_tag(v___x_2442_, 1);
                    lean_ctor_set(v___x_2442_, 1, v___x_2446_);
                    lean_ctor_set(v___x_2442_, 0, v_u_2437_);
                    v___x_2448_ = v___x_2442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_u_2437_);
                    lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2446_);
                    v___x_2448_ = v_reuseFailAlloc_2460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v___x_2448_, 2);
                v___x_2449_ = l_Lean_mkConst(v___x_2445_, v___x_2448_);
                lean_inc_ref_n(v_type_2436_, 2);
                v_inst_x27_2450_ = l_Lean_mkAppB(v___x_2449_, v_type_2436_, v_ringInst_2438_);
                v___x_2451_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2;
                lean_inc_n(v_toBind_2429_, 2);
                v___f_2452_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3 as *mut core::ffi::c_void,
                    8,
                    7,
                );
                lean_closure_set(v___f_2452_, 0, v___x_2451_);
                lean_closure_set(v___f_2452_, 1, v___x_2444_);
                lean_closure_set(v___f_2452_, 2, v___x_2448_);
                lean_closure_set(v___f_2452_, 3, v_type_2436_);
                lean_closure_set(v___f_2452_, 4, v_canonExpr_2439_);
                lean_closure_set(v___f_2452_, 5, v_toBind_2429_);
                lean_closure_set(v___f_2452_, 6, v___f_2430_);
                v___f_2453_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_2453_, 0, v___f_2452_);
                lean_inc_ref(v___f_2453_);
                v___f_2454_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7 as *mut core::ffi::c_void,
                    7,
                    6,
                );
                lean_closure_set(v___f_2454_, 0, v_toPure_2427_);
                lean_closure_set(v___f_2454_, 1, v_inst_x27_2450_);
                lean_closure_set(v___f_2454_, 2, v_toBind_2429_);
                lean_closure_set(v___f_2454_, 3, v___f_2453_);
                lean_closure_set(v___f_2454_, 4, v___f_2453_);
                lean_closure_set(v___f_2454_, 5, v_inst_2431_);
                v___x_2455_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3;
                v___x_2456_ = l_Lean_mkConst(v___x_2455_, v___x_2448_);
                v_instType_2457_ = l_Lean_Expr_app___override(v___x_2456_, v_type_2436_);
                v___x_2458_ = lean_apply_1(v_synthInstance_x3f_2440_, v_instType_2457_);
                v___x_2459_ = lean_apply_4(
                    v_toBind_2429_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_2462_: *mut LeanObject,
    mut v_inst_2463_: *mut LeanObject,
    mut v_inst_2464_: *mut LeanObject,
    mut v_inst_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2466_ = lean_ctor_get(v_inst_2463_, 0);
    lean_inc_ref(v_toApplicative_2466_);
    v_toBind_2467_ = lean_ctor_get(v_inst_2463_, 1);
    lean_inc_n(v_toBind_2467_, 3);
    lean_dec_ref(v_inst_2463_);
    v_getRing_2468_ = lean_ctor_get(v_inst_2465_, 0);
    lean_inc(v_getRing_2468_);
    v_modifyRing_2469_ = lean_ctor_get(v_inst_2465_, 1);
    lean_inc(v_modifyRing_2469_);
    lean_dec_ref(v_inst_2465_);
    v_toPure_2470_ = lean_ctor_get(v_toApplicative_2466_, 1);
    lean_inc_n(v_toPure_2470_, 2);
    lean_dec_ref(v_toApplicative_2466_);
    v___f_2471_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2471_, 0, v_toPure_2470_);
    lean_closure_set(v___f_2471_, 1, v_modifyRing_2469_);
    lean_closure_set(v___f_2471_, 2, v_toBind_2467_);
    v___f_2472_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2472_, 0, v_toPure_2470_);
    lean_closure_set(v___f_2472_, 1, v_inst_2464_);
    lean_closure_set(v___f_2472_, 2, v_toBind_2467_);
    lean_closure_set(v___f_2472_, 3, v___f_2471_);
    lean_closure_set(v___f_2472_, 4, v_inst_2462_);
    v___x_2473_ = lean_apply_4(
        v_toBind_2467_,
        lean_box(0),
        lean_box(0),
        v_getRing_2468_,
        v___f_2472_,
    );
    return v___x_2473_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getIntCastFn(
    mut v_m_2474_: *mut LeanObject,
    mut v_inst_2475_: *mut LeanObject,
    mut v_inst_2476_: *mut LeanObject,
    mut v_inst_2477_: *mut LeanObject,
    mut v_inst_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(
        v_inst_2475_,
        v_inst_2476_,
        v_inst_2477_,
        v_inst_2478_,
    );
    return v___x_2479_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(
    mut v_natCastFn_2480_: *mut LeanObject,
    mut v_s_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2502_: u8 = 0;
    let mut v_unused_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2482_ = lean_ctor_get(v_s_2481_, 0);
                v_type_2483_ = lean_ctor_get(v_s_2481_, 1);
                v_u_2484_ = lean_ctor_get(v_s_2481_, 2);
                v_ringInst_2485_ = lean_ctor_get(v_s_2481_, 3);
                v_semiringInst_2486_ = lean_ctor_get(v_s_2481_, 4);
                v_charInst_x3f_2487_ = lean_ctor_get(v_s_2481_, 5);
                v_addFn_x3f_2488_ = lean_ctor_get(v_s_2481_, 6);
                v_mulFn_x3f_2489_ = lean_ctor_get(v_s_2481_, 7);
                v_subFn_x3f_2490_ = lean_ctor_get(v_s_2481_, 8);
                v_negFn_x3f_2491_ = lean_ctor_get(v_s_2481_, 9);
                v_powFn_x3f_2492_ = lean_ctor_get(v_s_2481_, 10);
                v_intCastFn_x3f_2493_ = lean_ctor_get(v_s_2481_, 11);
                v_one_x3f_2494_ = lean_ctor_get(v_s_2481_, 13);
                v_isSharedCheck_2502_ = (!lean_is_exclusive(v_s_2481_)) as u8;
                if v_isSharedCheck_2502_ == 0 {
                    v_unused_2503_ = lean_ctor_get(v_s_2481_, 12);
                    lean_dec(v_unused_2503_);
                    v___x_2496_ = v_s_2481_;
                    v_isShared_2497_ = v_isSharedCheck_2502_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_one_x3f_2494_);
                    lean_inc(v_intCastFn_x3f_2493_);
                    lean_inc(v_powFn_x3f_2492_);
                    lean_inc(v_negFn_x3f_2491_);
                    lean_inc(v_subFn_x3f_2490_);
                    lean_inc(v_mulFn_x3f_2489_);
                    lean_inc(v_addFn_x3f_2488_);
                    lean_inc(v_charInst_x3f_2487_);
                    lean_inc(v_semiringInst_2486_);
                    lean_inc(v_ringInst_2485_);
                    lean_inc(v_u_2484_);
                    lean_inc(v_type_2483_);
                    lean_inc(v_id_2482_);
                    lean_dec(v_s_2481_);
                    v___x_2496_ = lean_box(0);
                    v_isShared_2497_ = v_isSharedCheck_2502_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2498_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2498_, 0, v_natCastFn_2480_);
                if v_isShared_2497_ == 0 {
                    lean_ctor_set(v___x_2496_, 12, v___x_2498_);
                    v___x_2500_ = v___x_2496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 14, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_id_2482_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_type_2483_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_u_2484_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_ringInst_2485_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_semiringInst_2486_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 5, v_charInst_x3f_2487_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 6, v_addFn_x3f_2488_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 7, v_mulFn_x3f_2489_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 8, v_subFn_x3f_2490_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 9, v_negFn_x3f_2491_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 10, v_powFn_x3f_2492_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 11, v_intCastFn_x3f_2493_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 12, v___x_2498_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 13, v_one_x3f_2494_);
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
    mut v_toPure_2504_: *mut LeanObject,
    mut v_natCastFn_2505_: *mut LeanObject,
    mut v_____r_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    v___x_2507_ = lean_apply_2(v_toPure_2504_, lean_box(0), v_natCastFn_2505_);
    return v___x_2507_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(
    mut v_toPure_2508_: *mut LeanObject,
    mut v_modifyRing_2509_: *mut LeanObject,
    mut v_toBind_2510_: *mut LeanObject,
    mut v_natCastFn_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_natCastFn_2511_);
    v___f_2512_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2512_, 0, v_natCastFn_2511_);
    v___f_2513_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2513_, 0, v_toPure_2508_);
    lean_closure_set(v___f_2513_, 1, v_natCastFn_2511_);
    v___x_2514_ = lean_apply_1(v_modifyRing_2509_, v___f_2512_);
    v___x_2515_ = lean_apply_4(
        v_toBind_2510_,
        lean_box(0),
        lean_box(0),
        v___x_2514_,
        v___f_2513_,
    );
    return v___x_2515_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(
    mut v_toPure_2516_: *mut LeanObject,
    mut v_inst_2517_: *mut LeanObject,
    mut v_inst_2518_: *mut LeanObject,
    mut v_inst_2519_: *mut LeanObject,
    mut v_toBind_2520_: *mut LeanObject,
    mut v___f_2521_: *mut LeanObject,
    mut v_ring_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natCastFn_x3f_2523_: *mut LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_2523_ = lean_ctor_get(v_ring_2522_, 12);
    if lean_obj_tag(v_natCastFn_x3f_2523_) == 1 {
        let mut v_val_2524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_natCastFn_x3f_2523_);
        lean_dec_ref(v_ring_2522_);
        lean_dec(v___f_2521_);
        lean_dec(v_toBind_2520_);
        lean_dec_ref(v_inst_2519_);
        lean_dec_ref(v_inst_2518_);
        lean_dec(v_inst_2517_);
        v_val_2524_ = lean_ctor_get(v_natCastFn_x3f_2523_, 0);
        lean_inc(v_val_2524_);
        lean_dec_ref_known(v_natCastFn_x3f_2523_, 1);
        v___x_2525_ = lean_apply_2(v_toPure_2516_, lean_box(0), v_val_2524_);
        return v___x_2525_;
    } else {
        let mut v_type_2526_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2527_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2516_);
        v_type_2526_ = lean_ctor_get(v_ring_2522_, 1);
        lean_inc_ref(v_type_2526_);
        v_u_2527_ = lean_ctor_get(v_ring_2522_, 2);
        lean_inc(v_u_2527_);
        v_semiringInst_2528_ = lean_ctor_get(v_ring_2522_, 4);
        lean_inc_ref(v_semiringInst_2528_);
        lean_dec_ref(v_ring_2522_);
        v___x_2529_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(
                v_inst_2517_,
                v_inst_2518_,
                v_inst_2519_,
                v_u_2527_,
                v_type_2526_,
                v_semiringInst_2528_,
            );
        v___x_2530_ = lean_apply_4(
            v_toBind_2520_,
            lean_box(0),
            lean_box(0),
            v___x_2529_,
            v___f_2521_,
        );
        return v___x_2530_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(
    mut v_inst_2531_: *mut LeanObject,
    mut v_inst_2532_: *mut LeanObject,
    mut v_inst_2533_: *mut LeanObject,
    mut v_inst_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2535_ = lean_ctor_get(v_inst_2532_, 0);
    v_toBind_2536_ = lean_ctor_get(v_inst_2532_, 1);
    lean_inc_n(v_toBind_2536_, 3);
    v_getRing_2537_ = lean_ctor_get(v_inst_2534_, 0);
    lean_inc(v_getRing_2537_);
    v_modifyRing_2538_ = lean_ctor_get(v_inst_2534_, 1);
    lean_inc(v_modifyRing_2538_);
    lean_dec_ref(v_inst_2534_);
    v_toPure_2539_ = lean_ctor_get(v_toApplicative_2535_, 1);
    lean_inc_n(v_toPure_2539_, 2);
    v___f_2540_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2540_, 0, v_toPure_2539_);
    lean_closure_set(v___f_2540_, 1, v_modifyRing_2538_);
    lean_closure_set(v___f_2540_, 2, v_toBind_2536_);
    v___f_2541_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2541_, 0, v_toPure_2539_);
    lean_closure_set(v___f_2541_, 1, v_inst_2531_);
    lean_closure_set(v___f_2541_, 2, v_inst_2532_);
    lean_closure_set(v___f_2541_, 3, v_inst_2533_);
    lean_closure_set(v___f_2541_, 4, v_toBind_2536_);
    lean_closure_set(v___f_2541_, 5, v___f_2540_);
    v___x_2542_ = lean_apply_4(
        v_toBind_2536_,
        lean_box(0),
        lean_box(0),
        v_getRing_2537_,
        v___f_2541_,
    );
    return v___x_2542_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn(
    mut v_m_2543_: *mut LeanObject,
    mut v_inst_2544_: *mut LeanObject,
    mut v_inst_2545_: *mut LeanObject,
    mut v_inst_2546_: *mut LeanObject,
    mut v_inst_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v___x_2548_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(
        v_inst_2544_,
        v_inst_2545_,
        v_inst_2546_,
        v_inst_2547_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(
    mut v_invFn_2549_: *mut LeanObject,
    mut v_s_2550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2551_ = lean_ctor_get(v_s_2550_, 0);
                v_semiringId_x3f_2552_ = lean_ctor_get(v_s_2550_, 2);
                v_commSemiringInst_2553_ = lean_ctor_get(v_s_2550_, 3);
                v_commRingInst_2554_ = lean_ctor_get(v_s_2550_, 4);
                v_noZeroDivInst_x3f_2555_ = lean_ctor_get(v_s_2550_, 5);
                v_fieldInst_x3f_2556_ = lean_ctor_get(v_s_2550_, 6);
                v_isSharedCheck_2564_ = (!lean_is_exclusive(v_s_2550_)) as u8;
                if v_isSharedCheck_2564_ == 0 {
                    v_unused_2565_ = lean_ctor_get(v_s_2550_, 1);
                    lean_dec(v_unused_2565_);
                    v___x_2558_ = v_s_2550_;
                    v_isShared_2559_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fieldInst_x3f_2556_);
                    lean_inc(v_noZeroDivInst_x3f_2555_);
                    lean_inc(v_commRingInst_2554_);
                    lean_inc(v_commSemiringInst_2553_);
                    lean_inc(v_semiringId_x3f_2552_);
                    lean_inc(v_toRing_2551_);
                    lean_dec(v_s_2550_);
                    v___x_2558_ = lean_box(0);
                    v_isShared_2559_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2560_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2560_, 0, v_invFn_2549_);
                if v_isShared_2559_ == 0 {
                    lean_ctor_set(v___x_2558_, 1, v___x_2560_);
                    v___x_2562_ = v___x_2558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_toRing_2551_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2560_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_semiringId_x3f_2552_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_commSemiringInst_2553_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_commRingInst_2554_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 5, v_noZeroDivInst_x3f_2555_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_fieldInst_x3f_2556_);
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
    mut v_toPure_2566_: *mut LeanObject,
    mut v_invFn_2567_: *mut LeanObject,
    mut v_____r_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    v___x_2569_ = lean_apply_2(v_toPure_2566_, lean_box(0), v_invFn_2567_);
    return v___x_2569_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(
    mut v_toPure_2570_: *mut LeanObject,
    mut v_modifyCommRing_2571_: *mut LeanObject,
    mut v_toBind_2572_: *mut LeanObject,
    mut v_invFn_2573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_invFn_2573_);
    v___f_2574_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2574_, 0, v_invFn_2573_);
    v___f_2575_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2575_, 0, v_toPure_2570_);
    lean_closure_set(v___f_2575_, 1, v_invFn_2573_);
    v___x_2576_ = lean_apply_1(v_modifyCommRing_2571_, v___f_2574_);
    v___x_2577_ = lean_apply_4(
        v_toBind_2572_,
        lean_box(0),
        lean_box(0),
        v___x_2576_,
        v___f_2575_,
    );
    return v___x_2577_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8() -> *mut LeanObject
{
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7;
    v___x_2594_ = l_Lean_stringToMessageData(v___x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(
    mut v_toPure_2595_: *mut LeanObject,
    mut v_inst_2596_: *mut LeanObject,
    mut v_inst_2597_: *mut LeanObject,
    mut v_inst_2598_: *mut LeanObject,
    mut v_inst_2599_: *mut LeanObject,
    mut v_toBind_2600_: *mut LeanObject,
    mut v___f_2601_: *mut LeanObject,
    mut v_ring_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fieldInst_x3f_2603_: *mut LeanObject = core::ptr::null_mut();
    v_fieldInst_x3f_2603_ = lean_ctor_get(v_ring_2602_, 6);
    if lean_obj_tag(v_fieldInst_x3f_2603_) == 1 {
        let mut v_invFn_x3f_2604_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_fieldInst_x3f_2603_);
        v_invFn_x3f_2604_ = lean_ctor_get(v_ring_2602_, 1);
        if lean_obj_tag(v_invFn_x3f_2604_) == 1 {
            let mut v_val_2605_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_invFn_x3f_2604_);
            lean_dec_ref_known(v_fieldInst_x3f_2603_, 1);
            lean_dec_ref(v_ring_2602_);
            lean_dec(v___f_2601_);
            lean_dec(v_toBind_2600_);
            lean_dec_ref(v_inst_2599_);
            lean_dec_ref(v_inst_2598_);
            lean_dec_ref(v_inst_2597_);
            lean_dec(v_inst_2596_);
            v_val_2605_ = lean_ctor_get(v_invFn_x3f_2604_, 0);
            lean_inc(v_val_2605_);
            lean_dec_ref_known(v_invFn_x3f_2604_, 1);
            v___x_2606_ = lean_apply_2(v_toPure_2595_, lean_box(0), v_val_2605_);
            return v___x_2606_;
        } else {
            let mut v_toRing_2607_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2608_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_2609_: *mut LeanObject = core::ptr::null_mut();
            let mut v_u_2610_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expectedInst_2615_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_2595_);
            v_toRing_2607_ = lean_ctor_get(v_ring_2602_, 0);
            lean_inc_ref(v_toRing_2607_);
            lean_dec_ref(v_ring_2602_);
            v_val_2608_ = lean_ctor_get(v_fieldInst_x3f_2603_, 0);
            lean_inc(v_val_2608_);
            lean_dec_ref_known(v_fieldInst_x3f_2603_, 1);
            v_type_2609_ = lean_ctor_get(v_toRing_2607_, 1);
            lean_inc_ref_n(v_type_2609_, 2);
            v_u_2610_ = lean_ctor_get(v_toRing_2607_, 2);
            lean_inc_n(v_u_2610_, 2);
            lean_dec_ref(v_toRing_2607_);
            v___x_2611_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2;
            v___x_2612_ = lean_box(0);
            v___x_2613_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2613_, 0, v_u_2610_);
            lean_ctor_set(v___x_2613_, 1, v___x_2612_);
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
            v___x_2619_ = lean_apply_4(
                v_toBind_2600_,
                lean_box(0),
                lean_box(0),
                v___x_2618_,
                v___f_2601_,
            );
            return v___x_2619_;
        }
    } else {
        let mut v_toRing_2620_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_2621_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2601_);
        lean_dec(v_toBind_2600_);
        lean_dec_ref(v_inst_2599_);
        lean_dec(v_inst_2596_);
        lean_dec(v_toPure_2595_);
        v_toRing_2620_ = lean_ctor_get(v_ring_2602_, 0);
        lean_inc_ref(v_toRing_2620_);
        lean_dec_ref(v_ring_2602_);
        v_type_2621_ = lean_ctor_get(v_toRing_2620_, 1);
        lean_inc_ref(v_type_2621_);
        lean_dec_ref(v_toRing_2620_);
        v___x_2622_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once
            ),
            _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8,
        );
        v___x_2623_ = l_Lean_indentExpr(v_type_2621_);
        v___x_2624_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2624_, 0, v___x_2622_);
        lean_ctor_set(v___x_2624_, 1, v___x_2623_);
        v___x_2625_ = l_Lean_throwError___redArg(v_inst_2598_, v_inst_2597_, v___x_2624_);
        return v___x_2625_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn___redArg(
    mut v_inst_2626_: *mut LeanObject,
    mut v_inst_2627_: *mut LeanObject,
    mut v_inst_2628_: *mut LeanObject,
    mut v_inst_2629_: *mut LeanObject,
    mut v_inst_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2631_ = lean_ctor_get(v_inst_2628_, 0);
    v_toBind_2632_ = lean_ctor_get(v_inst_2628_, 1);
    lean_inc_n(v_toBind_2632_, 3);
    v_getCommRing_2633_ = lean_ctor_get(v_inst_2630_, 0);
    lean_inc(v_getCommRing_2633_);
    v_modifyCommRing_2634_ = lean_ctor_get(v_inst_2630_, 1);
    lean_inc(v_modifyCommRing_2634_);
    lean_dec_ref(v_inst_2630_);
    v_toPure_2635_ = lean_ctor_get(v_toApplicative_2631_, 1);
    lean_inc_n(v_toPure_2635_, 2);
    v___f_2636_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2636_, 0, v_toPure_2635_);
    lean_closure_set(v___f_2636_, 1, v_modifyCommRing_2634_);
    lean_closure_set(v___f_2636_, 2, v_toBind_2632_);
    v___f_2637_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2637_, 0, v_toPure_2635_);
    lean_closure_set(v___f_2637_, 1, v_inst_2626_);
    lean_closure_set(v___f_2637_, 2, v_inst_2627_);
    lean_closure_set(v___f_2637_, 3, v_inst_2628_);
    lean_closure_set(v___f_2637_, 4, v_inst_2629_);
    lean_closure_set(v___f_2637_, 5, v_toBind_2632_);
    lean_closure_set(v___f_2637_, 6, v___f_2636_);
    v___x_2638_ = lean_apply_4(
        v_toBind_2632_,
        lean_box(0),
        lean_box(0),
        v_getCommRing_2633_,
        v___f_2637_,
    );
    return v___x_2638_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getInvFn(
    mut v_m_2639_: *mut LeanObject,
    mut v_inst_2640_: *mut LeanObject,
    mut v_inst_2641_: *mut LeanObject,
    mut v_inst_2642_: *mut LeanObject,
    mut v_inst_2643_: *mut LeanObject,
    mut v_inst_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_addFn_2646_: *mut LeanObject,
    mut v_s_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_unused_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2648_ = lean_ctor_get(v_s_2647_, 0);
                v_type_2649_ = lean_ctor_get(v_s_2647_, 1);
                v_u_2650_ = lean_ctor_get(v_s_2647_, 2);
                v_semiringInst_2651_ = lean_ctor_get(v_s_2647_, 3);
                v_mulFn_x3f_2652_ = lean_ctor_get(v_s_2647_, 5);
                v_powFn_x3f_2653_ = lean_ctor_get(v_s_2647_, 6);
                v_natCastFn_x3f_2654_ = lean_ctor_get(v_s_2647_, 7);
                v_isSharedCheck_2662_ = (!lean_is_exclusive(v_s_2647_)) as u8;
                if v_isSharedCheck_2662_ == 0 {
                    v_unused_2663_ = lean_ctor_get(v_s_2647_, 4);
                    lean_dec(v_unused_2663_);
                    v___x_2656_ = v_s_2647_;
                    v_isShared_2657_ = v_isSharedCheck_2662_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_natCastFn_x3f_2654_);
                    lean_inc(v_powFn_x3f_2653_);
                    lean_inc(v_mulFn_x3f_2652_);
                    lean_inc(v_semiringInst_2651_);
                    lean_inc(v_u_2650_);
                    lean_inc(v_type_2649_);
                    lean_inc(v_id_2648_);
                    lean_dec(v_s_2647_);
                    v___x_2656_ = lean_box(0);
                    v_isShared_2657_ = v_isSharedCheck_2662_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2658_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2658_, 0, v_addFn_2646_);
                if v_isShared_2657_ == 0 {
                    lean_ctor_set(v___x_2656_, 4, v___x_2658_);
                    v___x_2660_ = v___x_2656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_id_2648_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_type_2649_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_u_2650_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 3, v_semiringInst_2651_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 4, v___x_2658_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 5, v_mulFn_x3f_2652_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 6, v_powFn_x3f_2653_);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 7, v_natCastFn_x3f_2654_);
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
    mut v_toPure_2664_: *mut LeanObject,
    mut v_modifySemiring_2665_: *mut LeanObject,
    mut v_toBind_2666_: *mut LeanObject,
    mut v_addFn_2667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_addFn_2667_);
    v___f_2668_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2668_, 0, v_addFn_2667_);
    v___f_2669_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2669_, 0, v_toPure_2664_);
    lean_closure_set(v___f_2669_, 1, v_addFn_2667_);
    v___x_2670_ = lean_apply_1(v_modifySemiring_2665_, v___f_2668_);
    v___x_2671_ = lean_apply_4(
        v_toBind_2666_,
        lean_box(0),
        lean_box(0),
        v___x_2670_,
        v___f_2669_,
    );
    return v___x_2671_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(
    mut v_toPure_2672_: *mut LeanObject,
    mut v_inst_2673_: *mut LeanObject,
    mut v_inst_2674_: *mut LeanObject,
    mut v_inst_2675_: *mut LeanObject,
    mut v_inst_2676_: *mut LeanObject,
    mut v_toBind_2677_: *mut LeanObject,
    mut v___f_2678_: *mut LeanObject,
    mut v_sr_2679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addFn_x3f_2680_: *mut LeanObject = core::ptr::null_mut();
    v_addFn_x3f_2680_ = lean_ctor_get(v_sr_2679_, 4);
    if lean_obj_tag(v_addFn_x3f_2680_) == 1 {
        let mut v_val_2681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_addFn_x3f_2680_);
        lean_dec_ref(v_sr_2679_);
        lean_dec(v___f_2678_);
        lean_dec(v_toBind_2677_);
        lean_dec_ref(v_inst_2676_);
        lean_dec_ref(v_inst_2675_);
        lean_dec_ref(v_inst_2674_);
        lean_dec(v_inst_2673_);
        v_val_2681_ = lean_ctor_get(v_addFn_x3f_2680_, 0);
        lean_inc(v_val_2681_);
        lean_dec_ref_known(v_addFn_x3f_2680_, 1);
        v___x_2682_ = lean_apply_2(v_toPure_2672_, lean_box(0), v_val_2681_);
        return v___x_2682_;
    } else {
        let mut v_type_2683_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2684_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2672_);
        v_type_2683_ = lean_ctor_get(v_sr_2679_, 1);
        lean_inc_ref_n(v_type_2683_, 3);
        v_u_2684_ = lean_ctor_get(v_sr_2679_, 2);
        lean_inc_n(v_u_2684_, 2);
        v_semiringInst_2685_ = lean_ctor_get(v_sr_2679_, 3);
        lean_inc_ref(v_semiringInst_2685_);
        lean_dec_ref(v_sr_2679_);
        v___x_2686_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1;
        v___x_2687_ = lean_box(0);
        v___x_2688_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2688_, 0, v_u_2684_);
        lean_ctor_set(v___x_2688_, 1, v___x_2687_);
        lean_inc_ref(v___x_2688_);
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
        v___x_2697_ = lean_apply_4(
            v_toBind_2677_,
            lean_box(0),
            lean_box(0),
            v___x_2696_,
            v___f_2678_,
        );
        return v___x_2697_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(
    mut v_inst_2698_: *mut LeanObject,
    mut v_inst_2699_: *mut LeanObject,
    mut v_inst_2700_: *mut LeanObject,
    mut v_inst_2701_: *mut LeanObject,
    mut v_inst_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2703_ = lean_ctor_get(v_inst_2700_, 0);
    v_toBind_2704_ = lean_ctor_get(v_inst_2700_, 1);
    lean_inc_n(v_toBind_2704_, 3);
    v_getSemiring_2705_ = lean_ctor_get(v_inst_2702_, 0);
    lean_inc(v_getSemiring_2705_);
    v_modifySemiring_2706_ = lean_ctor_get(v_inst_2702_, 1);
    lean_inc(v_modifySemiring_2706_);
    lean_dec_ref(v_inst_2702_);
    v_toPure_2707_ = lean_ctor_get(v_toApplicative_2703_, 1);
    lean_inc_n(v_toPure_2707_, 2);
    v___f_2708_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2708_, 0, v_toPure_2707_);
    lean_closure_set(v___f_2708_, 1, v_modifySemiring_2706_);
    lean_closure_set(v___f_2708_, 2, v_toBind_2704_);
    v___f_2709_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2709_, 0, v_toPure_2707_);
    lean_closure_set(v___f_2709_, 1, v_inst_2698_);
    lean_closure_set(v___f_2709_, 2, v_inst_2699_);
    lean_closure_set(v___f_2709_, 3, v_inst_2700_);
    lean_closure_set(v___f_2709_, 4, v_inst_2701_);
    lean_closure_set(v___f_2709_, 5, v_toBind_2704_);
    lean_closure_set(v___f_2709_, 6, v___f_2708_);
    v___x_2710_ = lean_apply_4(
        v_toBind_2704_,
        lean_box(0),
        lean_box(0),
        v_getSemiring_2705_,
        v___f_2709_,
    );
    return v___x_2710_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getAddFn_x27(
    mut v_m_2711_: *mut LeanObject,
    mut v_inst_2712_: *mut LeanObject,
    mut v_inst_2713_: *mut LeanObject,
    mut v_inst_2714_: *mut LeanObject,
    mut v_inst_2715_: *mut LeanObject,
    mut v_inst_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_mulFn_2718_: *mut LeanObject,
    mut v_s_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_unused_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2720_ = lean_ctor_get(v_s_2719_, 0);
                v_type_2721_ = lean_ctor_get(v_s_2719_, 1);
                v_u_2722_ = lean_ctor_get(v_s_2719_, 2);
                v_semiringInst_2723_ = lean_ctor_get(v_s_2719_, 3);
                v_addFn_x3f_2724_ = lean_ctor_get(v_s_2719_, 4);
                v_powFn_x3f_2725_ = lean_ctor_get(v_s_2719_, 6);
                v_natCastFn_x3f_2726_ = lean_ctor_get(v_s_2719_, 7);
                v_isSharedCheck_2734_ = (!lean_is_exclusive(v_s_2719_)) as u8;
                if v_isSharedCheck_2734_ == 0 {
                    v_unused_2735_ = lean_ctor_get(v_s_2719_, 5);
                    lean_dec(v_unused_2735_);
                    v___x_2728_ = v_s_2719_;
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_natCastFn_x3f_2726_);
                    lean_inc(v_powFn_x3f_2725_);
                    lean_inc(v_addFn_x3f_2724_);
                    lean_inc(v_semiringInst_2723_);
                    lean_inc(v_u_2722_);
                    lean_inc(v_type_2721_);
                    lean_inc(v_id_2720_);
                    lean_dec(v_s_2719_);
                    v___x_2728_ = lean_box(0);
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2730_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2730_, 0, v_mulFn_2718_);
                if v_isShared_2729_ == 0 {
                    lean_ctor_set(v___x_2728_, 5, v___x_2730_);
                    v___x_2732_ = v___x_2728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_id_2720_);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_type_2721_);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_u_2722_);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_semiringInst_2723_);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_addFn_x3f_2724_);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 5, v___x_2730_);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 6, v_powFn_x3f_2725_);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 7, v_natCastFn_x3f_2726_);
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
    mut v_toPure_2736_: *mut LeanObject,
    mut v_modifySemiring_2737_: *mut LeanObject,
    mut v_toBind_2738_: *mut LeanObject,
    mut v_mulFn_2739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_mulFn_2739_);
    v___f_2740_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2740_, 0, v_mulFn_2739_);
    v___f_2741_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2741_, 0, v_toPure_2736_);
    lean_closure_set(v___f_2741_, 1, v_mulFn_2739_);
    v___x_2742_ = lean_apply_1(v_modifySemiring_2737_, v___f_2740_);
    v___x_2743_ = lean_apply_4(
        v_toBind_2738_,
        lean_box(0),
        lean_box(0),
        v___x_2742_,
        v___f_2741_,
    );
    return v___x_2743_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(
    mut v_toPure_2744_: *mut LeanObject,
    mut v_inst_2745_: *mut LeanObject,
    mut v_inst_2746_: *mut LeanObject,
    mut v_inst_2747_: *mut LeanObject,
    mut v_inst_2748_: *mut LeanObject,
    mut v_toBind_2749_: *mut LeanObject,
    mut v___f_2750_: *mut LeanObject,
    mut v_sr_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mulFn_x3f_2752_: *mut LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_2752_ = lean_ctor_get(v_sr_2751_, 5);
    if lean_obj_tag(v_mulFn_x3f_2752_) == 1 {
        let mut v_val_2753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_mulFn_x3f_2752_);
        lean_dec_ref(v_sr_2751_);
        lean_dec(v___f_2750_);
        lean_dec(v_toBind_2749_);
        lean_dec_ref(v_inst_2748_);
        lean_dec_ref(v_inst_2747_);
        lean_dec_ref(v_inst_2746_);
        lean_dec(v_inst_2745_);
        v_val_2753_ = lean_ctor_get(v_mulFn_x3f_2752_, 0);
        lean_inc(v_val_2753_);
        lean_dec_ref_known(v_mulFn_x3f_2752_, 1);
        v___x_2754_ = lean_apply_2(v_toPure_2744_, lean_box(0), v_val_2753_);
        return v___x_2754_;
    } else {
        let mut v_type_2755_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2756_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2744_);
        v_type_2755_ = lean_ctor_get(v_sr_2751_, 1);
        lean_inc_ref_n(v_type_2755_, 3);
        v_u_2756_ = lean_ctor_get(v_sr_2751_, 2);
        lean_inc_n(v_u_2756_, 2);
        v_semiringInst_2757_ = lean_ctor_get(v_sr_2751_, 3);
        lean_inc_ref(v_semiringInst_2757_);
        lean_dec_ref(v_sr_2751_);
        v___x_2758_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1;
        v___x_2759_ = lean_box(0);
        v___x_2760_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2760_, 0, v_u_2756_);
        lean_ctor_set(v___x_2760_, 1, v___x_2759_);
        lean_inc_ref(v___x_2760_);
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
        v___x_2769_ = lean_apply_4(
            v_toBind_2749_,
            lean_box(0),
            lean_box(0),
            v___x_2768_,
            v___f_2750_,
        );
        return v___x_2769_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(
    mut v_inst_2770_: *mut LeanObject,
    mut v_inst_2771_: *mut LeanObject,
    mut v_inst_2772_: *mut LeanObject,
    mut v_inst_2773_: *mut LeanObject,
    mut v_inst_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2775_ = lean_ctor_get(v_inst_2772_, 0);
    v_toBind_2776_ = lean_ctor_get(v_inst_2772_, 1);
    lean_inc_n(v_toBind_2776_, 3);
    v_getSemiring_2777_ = lean_ctor_get(v_inst_2774_, 0);
    lean_inc(v_getSemiring_2777_);
    v_modifySemiring_2778_ = lean_ctor_get(v_inst_2774_, 1);
    lean_inc(v_modifySemiring_2778_);
    lean_dec_ref(v_inst_2774_);
    v_toPure_2779_ = lean_ctor_get(v_toApplicative_2775_, 1);
    lean_inc_n(v_toPure_2779_, 2);
    v___f_2780_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2780_, 0, v_toPure_2779_);
    lean_closure_set(v___f_2780_, 1, v_modifySemiring_2778_);
    lean_closure_set(v___f_2780_, 2, v_toBind_2776_);
    v___f_2781_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2781_, 0, v_toPure_2779_);
    lean_closure_set(v___f_2781_, 1, v_inst_2770_);
    lean_closure_set(v___f_2781_, 2, v_inst_2771_);
    lean_closure_set(v___f_2781_, 3, v_inst_2772_);
    lean_closure_set(v___f_2781_, 4, v_inst_2773_);
    lean_closure_set(v___f_2781_, 5, v_toBind_2776_);
    lean_closure_set(v___f_2781_, 6, v___f_2780_);
    v___x_2782_ = lean_apply_4(
        v_toBind_2776_,
        lean_box(0),
        lean_box(0),
        v_getSemiring_2777_,
        v___f_2781_,
    );
    return v___x_2782_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getMulFn_x27(
    mut v_m_2783_: *mut LeanObject,
    mut v_inst_2784_: *mut LeanObject,
    mut v_inst_2785_: *mut LeanObject,
    mut v_inst_2786_: *mut LeanObject,
    mut v_inst_2787_: *mut LeanObject,
    mut v_inst_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_powFn_2790_: *mut LeanObject,
    mut v_s_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_unused_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2792_ = lean_ctor_get(v_s_2791_, 0);
                v_type_2793_ = lean_ctor_get(v_s_2791_, 1);
                v_u_2794_ = lean_ctor_get(v_s_2791_, 2);
                v_semiringInst_2795_ = lean_ctor_get(v_s_2791_, 3);
                v_addFn_x3f_2796_ = lean_ctor_get(v_s_2791_, 4);
                v_mulFn_x3f_2797_ = lean_ctor_get(v_s_2791_, 5);
                v_natCastFn_x3f_2798_ = lean_ctor_get(v_s_2791_, 7);
                v_isSharedCheck_2806_ = (!lean_is_exclusive(v_s_2791_)) as u8;
                if v_isSharedCheck_2806_ == 0 {
                    v_unused_2807_ = lean_ctor_get(v_s_2791_, 6);
                    lean_dec(v_unused_2807_);
                    v___x_2800_ = v_s_2791_;
                    v_isShared_2801_ = v_isSharedCheck_2806_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_natCastFn_x3f_2798_);
                    lean_inc(v_mulFn_x3f_2797_);
                    lean_inc(v_addFn_x3f_2796_);
                    lean_inc(v_semiringInst_2795_);
                    lean_inc(v_u_2794_);
                    lean_inc(v_type_2793_);
                    lean_inc(v_id_2792_);
                    lean_dec(v_s_2791_);
                    v___x_2800_ = lean_box(0);
                    v_isShared_2801_ = v_isSharedCheck_2806_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2802_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2802_, 0, v_powFn_2790_);
                if v_isShared_2801_ == 0 {
                    lean_ctor_set(v___x_2800_, 6, v___x_2802_);
                    v___x_2804_ = v___x_2800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_id_2792_);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_type_2793_);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_u_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_semiringInst_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_addFn_x3f_2796_);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 5, v_mulFn_x3f_2797_);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 6, v___x_2802_);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 7, v_natCastFn_x3f_2798_);
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
    mut v_toPure_2808_: *mut LeanObject,
    mut v_modifySemiring_2809_: *mut LeanObject,
    mut v_toBind_2810_: *mut LeanObject,
    mut v_powFn_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_powFn_2811_);
    v___f_2812_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2812_, 0, v_powFn_2811_);
    v___f_2813_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2813_, 0, v_toPure_2808_);
    lean_closure_set(v___f_2813_, 1, v_powFn_2811_);
    v___x_2814_ = lean_apply_1(v_modifySemiring_2809_, v___f_2812_);
    v___x_2815_ = lean_apply_4(
        v_toBind_2810_,
        lean_box(0),
        lean_box(0),
        v___x_2814_,
        v___f_2813_,
    );
    return v___x_2815_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(
    mut v_toPure_2816_: *mut LeanObject,
    mut v_inst_2817_: *mut LeanObject,
    mut v_inst_2818_: *mut LeanObject,
    mut v_inst_2819_: *mut LeanObject,
    mut v_inst_2820_: *mut LeanObject,
    mut v_toBind_2821_: *mut LeanObject,
    mut v___f_2822_: *mut LeanObject,
    mut v_sr_2823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_powFn_x3f_2824_: *mut LeanObject = core::ptr::null_mut();
    v_powFn_x3f_2824_ = lean_ctor_get(v_sr_2823_, 6);
    if lean_obj_tag(v_powFn_x3f_2824_) == 1 {
        let mut v_val_2825_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_powFn_x3f_2824_);
        lean_dec_ref(v_sr_2823_);
        lean_dec(v___f_2822_);
        lean_dec(v_toBind_2821_);
        lean_dec_ref(v_inst_2820_);
        lean_dec_ref(v_inst_2819_);
        lean_dec_ref(v_inst_2818_);
        lean_dec(v_inst_2817_);
        v_val_2825_ = lean_ctor_get(v_powFn_x3f_2824_, 0);
        lean_inc(v_val_2825_);
        lean_dec_ref_known(v_powFn_x3f_2824_, 1);
        v___x_2826_ = lean_apply_2(v_toPure_2816_, lean_box(0), v_val_2825_);
        return v___x_2826_;
    } else {
        let mut v_type_2827_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2828_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2829_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2816_);
        v_type_2827_ = lean_ctor_get(v_sr_2823_, 1);
        lean_inc_ref(v_type_2827_);
        v_u_2828_ = lean_ctor_get(v_sr_2823_, 2);
        lean_inc(v_u_2828_);
        v_semiringInst_2829_ = lean_ctor_get(v_sr_2823_, 3);
        lean_inc_ref(v_semiringInst_2829_);
        lean_dec_ref(v_sr_2823_);
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
        v___x_2831_ = lean_apply_4(
            v_toBind_2821_,
            lean_box(0),
            lean_box(0),
            v___x_2830_,
            v___f_2822_,
        );
        return v___x_2831_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(
    mut v_inst_2832_: *mut LeanObject,
    mut v_inst_2833_: *mut LeanObject,
    mut v_inst_2834_: *mut LeanObject,
    mut v_inst_2835_: *mut LeanObject,
    mut v_inst_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2837_ = lean_ctor_get(v_inst_2834_, 0);
    v_toBind_2838_ = lean_ctor_get(v_inst_2834_, 1);
    lean_inc_n(v_toBind_2838_, 3);
    v_getSemiring_2839_ = lean_ctor_get(v_inst_2836_, 0);
    lean_inc(v_getSemiring_2839_);
    v_modifySemiring_2840_ = lean_ctor_get(v_inst_2836_, 1);
    lean_inc(v_modifySemiring_2840_);
    lean_dec_ref(v_inst_2836_);
    v_toPure_2841_ = lean_ctor_get(v_toApplicative_2837_, 1);
    lean_inc_n(v_toPure_2841_, 2);
    v___f_2842_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2842_, 0, v_toPure_2841_);
    lean_closure_set(v___f_2842_, 1, v_modifySemiring_2840_);
    lean_closure_set(v___f_2842_, 2, v_toBind_2838_);
    v___f_2843_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2843_, 0, v_toPure_2841_);
    lean_closure_set(v___f_2843_, 1, v_inst_2832_);
    lean_closure_set(v___f_2843_, 2, v_inst_2833_);
    lean_closure_set(v___f_2843_, 3, v_inst_2834_);
    lean_closure_set(v___f_2843_, 4, v_inst_2835_);
    lean_closure_set(v___f_2843_, 5, v_toBind_2838_);
    lean_closure_set(v___f_2843_, 6, v___f_2842_);
    v___x_2844_ = lean_apply_4(
        v_toBind_2838_,
        lean_box(0),
        lean_box(0),
        v_getSemiring_2839_,
        v___f_2843_,
    );
    return v___x_2844_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getPowFn_x27(
    mut v_m_2845_: *mut LeanObject,
    mut v_inst_2846_: *mut LeanObject,
    mut v_inst_2847_: *mut LeanObject,
    mut v_inst_2848_: *mut LeanObject,
    mut v_inst_2849_: *mut LeanObject,
    mut v_inst_2850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_natCastFn_2852_: *mut LeanObject,
    mut v_s_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_unused_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2854_ = lean_ctor_get(v_s_2853_, 0);
                v_type_2855_ = lean_ctor_get(v_s_2853_, 1);
                v_u_2856_ = lean_ctor_get(v_s_2853_, 2);
                v_semiringInst_2857_ = lean_ctor_get(v_s_2853_, 3);
                v_addFn_x3f_2858_ = lean_ctor_get(v_s_2853_, 4);
                v_mulFn_x3f_2859_ = lean_ctor_get(v_s_2853_, 5);
                v_powFn_x3f_2860_ = lean_ctor_get(v_s_2853_, 6);
                v_isSharedCheck_2868_ = (!lean_is_exclusive(v_s_2853_)) as u8;
                if v_isSharedCheck_2868_ == 0 {
                    v_unused_2869_ = lean_ctor_get(v_s_2853_, 7);
                    lean_dec(v_unused_2869_);
                    v___x_2862_ = v_s_2853_;
                    v_isShared_2863_ = v_isSharedCheck_2868_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_powFn_x3f_2860_);
                    lean_inc(v_mulFn_x3f_2859_);
                    lean_inc(v_addFn_x3f_2858_);
                    lean_inc(v_semiringInst_2857_);
                    lean_inc(v_u_2856_);
                    lean_inc(v_type_2855_);
                    lean_inc(v_id_2854_);
                    lean_dec(v_s_2853_);
                    v___x_2862_ = lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2868_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2864_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2864_, 0, v_natCastFn_2852_);
                if v_isShared_2863_ == 0 {
                    lean_ctor_set(v___x_2862_, 7, v___x_2864_);
                    v___x_2866_ = v___x_2862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_id_2854_);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_type_2855_);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_u_2856_);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 3, v_semiringInst_2857_);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 4, v_addFn_x3f_2858_);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 5, v_mulFn_x3f_2859_);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 6, v_powFn_x3f_2860_);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 7, v___x_2864_);
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
    mut v_toPure_2870_: *mut LeanObject,
    mut v_modifySemiring_2871_: *mut LeanObject,
    mut v_toBind_2872_: *mut LeanObject,
    mut v_natCastFn_2873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_natCastFn_2873_);
    v___f_2874_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2874_, 0, v_natCastFn_2873_);
    v___f_2875_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2875_, 0, v_toPure_2870_);
    lean_closure_set(v___f_2875_, 1, v_natCastFn_2873_);
    v___x_2876_ = lean_apply_1(v_modifySemiring_2871_, v___f_2874_);
    v___x_2877_ = lean_apply_4(
        v_toBind_2872_,
        lean_box(0),
        lean_box(0),
        v___x_2876_,
        v___f_2875_,
    );
    return v___x_2877_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(
    mut v_toPure_2878_: *mut LeanObject,
    mut v_inst_2879_: *mut LeanObject,
    mut v_inst_2880_: *mut LeanObject,
    mut v_inst_2881_: *mut LeanObject,
    mut v_toBind_2882_: *mut LeanObject,
    mut v___f_2883_: *mut LeanObject,
    mut v_sr_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natCastFn_x3f_2885_: *mut LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_2885_ = lean_ctor_get(v_sr_2884_, 7);
    if lean_obj_tag(v_natCastFn_x3f_2885_) == 1 {
        let mut v_val_2886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_natCastFn_x3f_2885_);
        lean_dec_ref(v_sr_2884_);
        lean_dec(v___f_2883_);
        lean_dec(v_toBind_2882_);
        lean_dec_ref(v_inst_2881_);
        lean_dec_ref(v_inst_2880_);
        lean_dec(v_inst_2879_);
        v_val_2886_ = lean_ctor_get(v_natCastFn_x3f_2885_, 0);
        lean_inc(v_val_2886_);
        lean_dec_ref_known(v_natCastFn_x3f_2885_, 1);
        v___x_2887_ = lean_apply_2(v_toPure_2878_, lean_box(0), v_val_2886_);
        return v___x_2887_;
    } else {
        let mut v_type_2888_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2889_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2878_);
        v_type_2888_ = lean_ctor_get(v_sr_2884_, 1);
        lean_inc_ref(v_type_2888_);
        v_u_2889_ = lean_ctor_get(v_sr_2884_, 2);
        lean_inc(v_u_2889_);
        v_semiringInst_2890_ = lean_ctor_get(v_sr_2884_, 3);
        lean_inc_ref(v_semiringInst_2890_);
        lean_dec_ref(v_sr_2884_);
        v___x_2891_ =
            l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(
                v_inst_2879_,
                v_inst_2880_,
                v_inst_2881_,
                v_u_2889_,
                v_type_2888_,
                v_semiringInst_2890_,
            );
        v___x_2892_ = lean_apply_4(
            v_toBind_2882_,
            lean_box(0),
            lean_box(0),
            v___x_2891_,
            v___f_2883_,
        );
        return v___x_2892_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(
    mut v_inst_2893_: *mut LeanObject,
    mut v_inst_2894_: *mut LeanObject,
    mut v_inst_2895_: *mut LeanObject,
    mut v_inst_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2897_ = lean_ctor_get(v_inst_2894_, 0);
    v_toBind_2898_ = lean_ctor_get(v_inst_2894_, 1);
    lean_inc_n(v_toBind_2898_, 3);
    v_getSemiring_2899_ = lean_ctor_get(v_inst_2896_, 0);
    lean_inc(v_getSemiring_2899_);
    v_modifySemiring_2900_ = lean_ctor_get(v_inst_2896_, 1);
    lean_inc(v_modifySemiring_2900_);
    lean_dec_ref(v_inst_2896_);
    v_toPure_2901_ = lean_ctor_get(v_toApplicative_2897_, 1);
    lean_inc_n(v_toPure_2901_, 2);
    v___f_2902_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2902_, 0, v_toPure_2901_);
    lean_closure_set(v___f_2902_, 1, v_modifySemiring_2900_);
    lean_closure_set(v___f_2902_, 2, v_toBind_2898_);
    v___f_2903_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2903_, 0, v_toPure_2901_);
    lean_closure_set(v___f_2903_, 1, v_inst_2893_);
    lean_closure_set(v___f_2903_, 2, v_inst_2894_);
    lean_closure_set(v___f_2903_, 3, v_inst_2895_);
    lean_closure_set(v___f_2903_, 4, v_toBind_2898_);
    lean_closure_set(v___f_2903_, 5, v___f_2902_);
    v___x_2904_ = lean_apply_4(
        v_toBind_2898_,
        lean_box(0),
        lean_box(0),
        v_getSemiring_2899_,
        v___f_2903_,
    );
    return v___x_2904_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getNatCastFn_x27(
    mut v_m_2905_: *mut LeanObject,
    mut v_inst_2906_: *mut LeanObject,
    mut v_inst_2907_: *mut LeanObject,
    mut v_inst_2908_: *mut LeanObject,
    mut v_inst_2909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    v___x_2910_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(
        v_inst_2906_,
        v_inst_2907_,
        v_inst_2908_,
        v_inst_2909_,
    );
    return v___x_2910_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Functions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Functions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Functions(builtin);
}

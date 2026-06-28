// Lean compiler output
// Module: Lean.Meta.Sym.SynthInstance
// Imports: Lean.Meta.Sym.SymM Lean.Meta.SynthInstance
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppFn, l_Lean_Expr_hash,
    l_Lean_Int_mkInstHAdd, l_Lean_Int_mkInstHDiv, l_Lean_Int_mkInstHMod, l_Lean_Int_mkInstHMul,
    l_Lean_Int_mkInstHPow, l_Lean_Int_mkInstHSub, l_Lean_Int_mkInstLE, l_Lean_Int_mkInstLT,
    l_Lean_Int_mkType, l_Lean_Nat_mkInstHAdd, l_Lean_Nat_mkInstHDiv, l_Lean_Nat_mkInstHMod,
    l_Lean_Nat_mkInstHMul, l_Lean_Nat_mkInstHPow, l_Lean_Nat_mkInstHSub, l_Lean_Nat_mkInstLE,
    l_Lean_Nat_mkInstLT, l_Lean_Nat_mkType, l_Lean_mkApp3, l_Lean_mkConst,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_isDefEqStuckExceptionId, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    initialize_Lean_Meta_SynthInstance, l_Lean_Meta_synthInstanceCore_x3f,
    runtime_initialize_Lean_Meta_SynthInstance,
};
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__3_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__8_value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__13_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__18_value) as *mut crate::leanh::LeanObject,11858238400308895562 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__23_value) as *mut crate::leanh::LeanObject,13744984671752750173 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__28_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__33_value) as *mut crate::leanh::LeanObject,17878876274162330439 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__40_value) as *mut crate::leanh::LeanObject,8347582161988589016 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0_value: crate::leanh::LeanStringObject<
    24,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        115, 121, 109, 32, 116, 121, 112, 101, 99, 108, 97, 115, 115, 32, 105, 110, 102, 101, 114,
        101, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_synthInstance___closed__0_value: crate::leanh::LeanStringObject<30> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            96, 115, 121, 109, 96, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105,
            110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0,
        ],
    };
static mut l_Lean_Meta_Sym_synthInstance___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_synthInstance___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_synthInstance___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_synthInstance___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_x_752_: *mut crate::leanh::LeanObject,
    mut v_x_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_759_: u8 = 0;
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u64 = 0;
    let mut v___x_762_: u64 = 0;
    let mut v___x_763_: u64 = 0;
    let mut v_fold_764_: u64 = 0;
    let mut v___x_765_: u64 = 0;
    let mut v___x_766_: u64 = 0;
    let mut v___x_767_: u64 = 0;
    let mut v___x_768_: usize = 0;
    let mut v___x_769_: usize = 0;
    let mut v___x_770_: usize = 0;
    let mut v___x_771_: usize = 0;
    let mut v___x_772_: usize = 0;
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_753_) == 0 {
                    return v_x_752_;
                } else {
                    v_key_754_ = crate::leanh::lean_ctor_get(v_x_753_, 0);
                    v_value_755_ = crate::leanh::lean_ctor_get(v_x_753_, 1);
                    v_tail_756_ = crate::leanh::lean_ctor_get(v_x_753_, 2);
                    v_isSharedCheck_779_ = (!crate::leanh::lean_is_exclusive(v_x_753_)) as u8;
                    if v_isSharedCheck_779_ == 0 {
                        v___x_758_ = v_x_753_;
                        v_isShared_759_ = v_isSharedCheck_779_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_756_);
                        crate::leanh::lean_inc(v_value_755_);
                        crate::leanh::lean_inc(v_key_754_);
                        crate::leanh::lean_dec(v_x_753_);
                        v___x_758_ = crate::leanh::lean_box(0);
                        v_isShared_759_ = v_isSharedCheck_779_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_760_ = lean_array_get_size(v_x_752_);
                v___x_761_ = l_Lean_Expr_hash(v_key_754_);
                v___x_762_ = 32u64;
                v___x_763_ = lean_uint64_shift_right(v___x_761_, v___x_762_);
                v_fold_764_ = lean_uint64_xor(v___x_761_, v___x_763_);
                v___x_765_ = 16u64;
                v___x_766_ = lean_uint64_shift_right(v_fold_764_, v___x_765_);
                v___x_767_ = lean_uint64_xor(v_fold_764_, v___x_766_);
                v___x_768_ = lean_uint64_to_usize(v___x_767_);
                v___x_769_ = lean_usize_of_nat(v___x_760_);
                v___x_770_ = 1usize;
                v___x_771_ = lean_usize_sub(v___x_769_, v___x_770_);
                v___x_772_ = lean_usize_land(v___x_768_, v___x_771_);
                v___x_773_ = lean_array_uget_borrowed(v_x_752_, v___x_772_);
                crate::leanh::lean_inc(v___x_773_);
                if v_isShared_759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_758_, 2, v___x_773_);
                    v___x_775_ = v___x_758_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_778_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_778_, 0, v_key_754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_778_, 1, v_value_755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_778_, 2, v___x_773_);
                    v___x_775_ = v_reuseFailAlloc_778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_776_ = lean_array_uset(v_x_752_, v___x_772_, v___x_775_);
                v_x_752_ = v___x_776_;
                v_x_753_ = v_tail_756_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_i_780_: *mut crate::leanh::LeanObject,
    mut v_source_781_: *mut crate::leanh::LeanObject,
    mut v_target_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v_es_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_783_ = lean_array_get_size(v_source_781_);
                v___x_784_ = lean_nat_dec_lt(v_i_780_, v___x_783_);
                if v___x_784_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_781_);
                    crate::leanh::lean_dec(v_i_780_);
                    return v_target_782_;
                } else {
                    v_es_785_ = lean_array_fget(v_source_781_, v_i_780_);
                    v___x_786_ = crate::leanh::lean_box(0);
                    v_source_787_ = lean_array_fset(v_source_781_, v_i_780_, v___x_786_);
                    v_target_788_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_782_, v_es_785_);
                    v___x_789_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_790_ = lean_nat_add(v_i_780_, v___x_789_);
                    crate::leanh::lean_dec(v_i_780_);
                    v_i_780_ = v___x_790_;
                    v_source_781_ = v_source_787_;
                    v_target_782_ = v_target_788_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2___redArg(
    mut v_data_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = lean_array_get_size(v_data_792_);
    v___x_794_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_795_ = lean_nat_mul(v___x_793_, v___x_794_);
    v___x_796_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_797_ = crate::leanh::lean_box(0);
    v___x_798_ = lean_mk_array(v_nbuckets_795_, v___x_797_);
    v___x_799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v___x_796_, v_data_792_, v___x_798_);
    return v___x_799_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_x_801_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_802_: u8 = 0;
    let mut v_key_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_801_) == 0 {
                    v___x_802_ = 0;
                    return v___x_802_;
                } else {
                    v_key_803_ = crate::leanh::lean_ctor_get(v_x_801_, 0);
                    v_tail_804_ = crate::leanh::lean_ctor_get(v_x_801_, 2);
                    v___x_805_ = lean_expr_eqv(v_key_803_, v_a_800_);
                    if v___x_805_ == 0 {
                        v_x_801_ = v_tail_804_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_805_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_x_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_809_: u8 = 0;
    let mut v_r_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(v_a_807_, v_x_808_);
    crate::leanh::lean_dec(v_x_808_);
    crate::leanh::lean_dec_ref(v_a_807_);
    v_r_810_ = crate::leanh::lean_box((v_res_809_) as usize);
    return v_r_810_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(
    mut v_a_811_: *mut crate::leanh::LeanObject,
    mut v_b_812_: *mut crate::leanh::LeanObject,
    mut v_x_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_819_: u8 = 0;
    let mut v___x_820_: u8 = 0;
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_813_) == 0 {
                    crate::leanh::lean_dec(v_b_812_);
                    crate::leanh::lean_dec_ref(v_a_811_);
                    return v_x_813_;
                } else {
                    v_key_814_ = crate::leanh::lean_ctor_get(v_x_813_, 0);
                    v_value_815_ = crate::leanh::lean_ctor_get(v_x_813_, 1);
                    v_tail_816_ = crate::leanh::lean_ctor_get(v_x_813_, 2);
                    v_isSharedCheck_828_ = (!crate::leanh::lean_is_exclusive(v_x_813_)) as u8;
                    if v_isSharedCheck_828_ == 0 {
                        v___x_818_ = v_x_813_;
                        v_isShared_819_ = v_isSharedCheck_828_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_816_);
                        crate::leanh::lean_inc(v_value_815_);
                        crate::leanh::lean_inc(v_key_814_);
                        crate::leanh::lean_dec(v_x_813_);
                        v___x_818_ = crate::leanh::lean_box(0);
                        v_isShared_819_ = v_isSharedCheck_828_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_820_ = lean_expr_eqv(v_key_814_, v_a_811_);
                if v___x_820_ == 0 {
                    v___x_821_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(v_a_811_, v_b_812_, v_tail_816_);
                    if v_isShared_819_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_818_, 2, v___x_821_);
                        v___x_823_ = v___x_818_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_824_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 0, v_key_814_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 1, v_value_815_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 2, v___x_821_);
                        v___x_823_ = v_reuseFailAlloc_824_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_815_);
                    crate::leanh::lean_dec(v_key_814_);
                    if v_isShared_819_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_818_, 1, v_b_812_);
                        crate::leanh::lean_ctor_set(v___x_818_, 0, v_a_811_);
                        v___x_826_ = v___x_818_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_827_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_811_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 1, v_b_812_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 2, v_tail_816_);
                        v___x_826_ = v_reuseFailAlloc_827_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_823_;
            }
            3 => {
                return v___x_826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(
    mut v_m_829_: *mut crate::leanh::LeanObject,
    mut v_a_830_: *mut crate::leanh::LeanObject,
    mut v_b_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: u64 = 0;
    let mut v___x_839_: u64 = 0;
    let mut v___x_840_: u64 = 0;
    let mut v_fold_841_: u64 = 0;
    let mut v___x_842_: u64 = 0;
    let mut v___x_843_: u64 = 0;
    let mut v___x_844_: u64 = 0;
    let mut v___x_845_: usize = 0;
    let mut v___x_846_: usize = 0;
    let mut v___x_847_: usize = 0;
    let mut v___x_848_: usize = 0;
    let mut v___x_849_: usize = 0;
    let mut v_bkt_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v_val_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_832_ = crate::leanh::lean_ctor_get(v_m_829_, 0);
                v_buckets_833_ = crate::leanh::lean_ctor_get(v_m_829_, 1);
                v_isSharedCheck_876_ = (!crate::leanh::lean_is_exclusive(v_m_829_)) as u8;
                if v_isSharedCheck_876_ == 0 {
                    v___x_835_ = v_m_829_;
                    v_isShared_836_ = v_isSharedCheck_876_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_833_);
                    crate::leanh::lean_inc(v_size_832_);
                    crate::leanh::lean_dec(v_m_829_);
                    v___x_835_ = crate::leanh::lean_box(0);
                    v_isShared_836_ = v_isSharedCheck_876_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_837_ = lean_array_get_size(v_buckets_833_);
                v___x_838_ = l_Lean_Expr_hash(v_a_830_);
                v___x_839_ = 32u64;
                v___x_840_ = lean_uint64_shift_right(v___x_838_, v___x_839_);
                v_fold_841_ = lean_uint64_xor(v___x_838_, v___x_840_);
                v___x_842_ = 16u64;
                v___x_843_ = lean_uint64_shift_right(v_fold_841_, v___x_842_);
                v___x_844_ = lean_uint64_xor(v_fold_841_, v___x_843_);
                v___x_845_ = lean_uint64_to_usize(v___x_844_);
                v___x_846_ = lean_usize_of_nat(v___x_837_);
                v___x_847_ = 1usize;
                v___x_848_ = lean_usize_sub(v___x_846_, v___x_847_);
                v___x_849_ = lean_usize_land(v___x_845_, v___x_848_);
                v_bkt_850_ = lean_array_uget_borrowed(v_buckets_833_, v___x_849_);
                v___x_851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(v_a_830_, v_bkt_850_);
                if v___x_851_ == 0 {
                    v___x_852_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_853_ = lean_nat_add(v_size_832_, v___x_852_);
                    crate::leanh::lean_dec(v_size_832_);
                    crate::leanh::lean_inc(v_bkt_850_);
                    v___x_854_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_854_, 0, v_a_830_);
                    crate::leanh::lean_ctor_set(v___x_854_, 1, v_b_831_);
                    crate::leanh::lean_ctor_set(v___x_854_, 2, v_bkt_850_);
                    v_buckets_x27_855_ = lean_array_uset(v_buckets_833_, v___x_849_, v___x_854_);
                    v___x_856_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_857_ = lean_nat_mul(v_size_x27_853_, v___x_856_);
                    v___x_858_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_859_ = lean_nat_div(v___x_857_, v___x_858_);
                    crate::leanh::lean_dec(v___x_857_);
                    v___x_860_ = lean_array_get_size(v_buckets_x27_855_);
                    v___x_861_ = lean_nat_dec_le(v___x_859_, v___x_860_);
                    crate::leanh::lean_dec(v___x_859_);
                    if v___x_861_ == 0 {
                        v_val_862_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2___redArg(v_buckets_x27_855_);
                        if v_isShared_836_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_835_, 1, v_val_862_);
                            crate::leanh::lean_ctor_set(v___x_835_, 0, v_size_x27_853_);
                            v___x_864_ = v___x_835_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_865_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_865_, 0, v_size_x27_853_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_865_, 1, v_val_862_);
                            v___x_864_ = v_reuseFailAlloc_865_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_836_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_835_, 1, v_buckets_x27_855_);
                            crate::leanh::lean_ctor_set(v___x_835_, 0, v_size_x27_853_);
                            v___x_867_ = v___x_835_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v_size_x27_853_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_868_,
                                1,
                                v_buckets_x27_855_,
                            );
                            v___x_867_ = v_reuseFailAlloc_868_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_850_);
                    v___x_869_ = crate::leanh::lean_box(0);
                    v_buckets_x27_870_ = lean_array_uset(v_buckets_833_, v___x_849_, v___x_869_);
                    v___x_871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(v_a_830_, v_b_831_, v_bkt_850_);
                    v___x_872_ = lean_array_uset(v_buckets_x27_870_, v___x_849_, v___x_871_);
                    if v_isShared_836_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_835_, 1, v___x_872_);
                        v___x_874_ = v___x_835_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 0, v_size_832_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
                        v___x_874_ = v_reuseFailAlloc_875_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_864_;
            }
            3 => {
                return v___x_867_;
            }
            4 => {
                return v___x_874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(
    mut v_as_x27_877_: *mut crate::leanh::LeanObject,
    mut v_b_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_877_) == 0 {
                    return v_b_878_;
                } else {
                    v_head_879_ = crate::leanh::lean_ctor_get(v_as_x27_877_, 0);
                    v_tail_880_ = crate::leanh::lean_ctor_get(v_as_x27_877_, 1);
                    v_fst_881_ = crate::leanh::lean_ctor_get(v_head_879_, 0);
                    v_snd_882_ = crate::leanh::lean_ctor_get(v_head_879_, 1);
                    crate::leanh::lean_inc(v_snd_882_);
                    crate::leanh::lean_inc(v_fst_881_);
                    v_r_883_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(v_b_878_, v_fst_881_, v_snd_882_);
                    v_as_x27_877_ = v_tail_880_;
                    v_b_878_ = v_r_883_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg___boxed(
    mut v_as_x27_885_: *mut crate::leanh::LeanObject,
    mut v_b_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v_as_x27_885_, v_b_886_);
    crate::leanh::lean_dec(v_as_x27_885_);
    return v_res_887_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0(
    mut v_m_888_: *mut crate::leanh::LeanObject,
    mut v_l_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v_l_889_, v_m_888_);
    return v___x_890_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0___boxed(
    mut v_m_891_: *mut crate::leanh::LeanObject,
    mut v_l_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_893_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0(v_m_891_, v_l_892_);
    crate::leanh::lean_dec(v_l_892_);
    return v_res_893_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v_us_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_us_906_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2;
    v___x_907_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__4;
    v___x_908_ = l_Lean_mkConst(v___x_907_, v_us_906_);
    return v___x_908_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_909_ = l_Lean_Nat_mkType;
    v___x_910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5,
    );
    v___x_911_ = l_Lean_mkApp3(v___x_910_, v_nat_909_, v_nat_909_, v_nat_909_);
    return v___x_911_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = l_Lean_Nat_mkInstHAdd;
    v___x_913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__6,
    );
    v___x_914_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_914_, 0, v___x_913_);
    crate::leanh::lean_ctor_set(v___x_914_, 1, v___x_912_);
    return v___x_914_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v_us_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_us_918_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2;
    v___x_919_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__9;
    v___x_920_ = l_Lean_mkConst(v___x_919_, v_us_918_);
    return v___x_920_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_921_ = l_Lean_Nat_mkType;
    v___x_922_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10,
    );
    v___x_923_ = l_Lean_mkApp3(v___x_922_, v_nat_921_, v_nat_921_, v_nat_921_);
    return v___x_923_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Lean_Nat_mkInstHSub;
    v___x_925_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__11,
    );
    v___x_926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_925_);
    crate::leanh::lean_ctor_set(v___x_926_, 1, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v_us_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_us_930_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2;
    v___x_931_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__14;
    v___x_932_ = l_Lean_mkConst(v___x_931_, v_us_930_);
    return v___x_932_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_933_ = l_Lean_Nat_mkType;
    v___x_934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15,
    );
    v___x_935_ = l_Lean_mkApp3(v___x_934_, v_nat_933_, v_nat_933_, v_nat_933_);
    return v___x_935_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = l_Lean_Nat_mkInstHMul;
    v___x_937_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__16,
    );
    v___x_938_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_938_, 0, v___x_937_);
    crate::leanh::lean_ctor_set(v___x_938_, 1, v___x_936_);
    return v___x_938_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v_us_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_us_942_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2;
    v___x_943_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__19;
    v___x_944_ = l_Lean_mkConst(v___x_943_, v_us_942_);
    return v___x_944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_945_ = l_Lean_Nat_mkType;
    v___x_946_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20,
    );
    v___x_947_ = l_Lean_mkApp3(v___x_946_, v_nat_945_, v_nat_945_, v_nat_945_);
    return v___x_947_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_948_ = l_Lean_Nat_mkInstHDiv;
    v___x_949_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__21,
    );
    v___x_950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_949_);
    crate::leanh::lean_ctor_set(v___x_950_, 1, v___x_948_);
    return v___x_950_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v_us_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_us_954_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2;
    v___x_955_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__24;
    v___x_956_ = l_Lean_mkConst(v___x_955_, v_us_954_);
    return v___x_956_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_957_ = l_Lean_Nat_mkType;
    v___x_958_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25,
    );
    v___x_959_ = l_Lean_mkApp3(v___x_958_, v_nat_957_, v_nat_957_, v_nat_957_);
    return v___x_959_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = l_Lean_Nat_mkInstHMod;
    v___x_961_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__26,
    );
    v___x_962_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_962_, 0, v___x_961_);
    crate::leanh::lean_ctor_set(v___x_962_, 1, v___x_960_);
    return v___x_962_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v_us_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_us_966_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__2;
    v___x_967_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__29;
    v___x_968_ = l_Lean_mkConst(v___x_967_, v_us_966_);
    return v___x_968_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_969_ = l_Lean_Nat_mkType;
    v___x_970_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30,
    );
    v___x_971_ = l_Lean_mkApp3(v___x_970_, v_nat_969_, v_nat_969_, v_nat_969_);
    return v___x_971_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l_Lean_Nat_mkInstHPow;
    v___x_973_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__31,
    );
    v___x_974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_974_, 0, v___x_973_);
    crate::leanh::lean_ctor_set(v___x_974_, 1, v___x_972_);
    return v___x_974_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_979_ = l_Lean_Level_ofNat(v___x_978_);
    return v___x_979_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = crate::leanh::lean_box(0);
    v___x_981_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__35,
    );
    v___x_982_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
    crate::leanh::lean_ctor_set(v___x_982_, 1, v___x_980_);
    return v___x_982_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36,
    );
    v___x_984_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__34;
    v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_983_);
    return v___x_985_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_986_ = l_Lean_Nat_mkType;
    v___x_987_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37,
    );
    v___x_988_ = l_Lean_Expr_app___override(v___x_987_, v_nat_986_);
    return v___x_988_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = l_Lean_Nat_mkInstLT;
    v___x_990_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__38,
    );
    v___x_991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_991_, 0, v___x_990_);
    crate::leanh::lean_ctor_set(v___x_991_, 1, v___x_989_);
    return v___x_991_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__36,
    );
    v___x_996_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__41;
    v___x_997_ = l_Lean_mkConst(v___x_996_, v___x_995_);
    return v___x_997_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_998_ = l_Lean_Nat_mkType;
    v___x_999_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42,
    );
    v___x_1000_ = l_Lean_Expr_app___override(v___x_999_, v_nat_998_);
    return v___x_1000_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = l_Lean_Nat_mkInstLE;
    v___x_1002_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__43,
    );
    v___x_1003_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1003_, 0, v___x_1002_);
    crate::leanh::lean_ctor_set(v___x_1003_, 1, v___x_1001_);
    return v___x_1003_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v_int_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_int_1004_ = l_Lean_Int_mkType;
    v___x_1005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__5,
    );
    v___x_1006_ = l_Lean_mkApp3(v___x_1005_, v_int_1004_, v_int_1004_, v_int_1004_);
    return v___x_1006_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = l_Lean_Int_mkInstHAdd;
    v___x_1008_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__45,
    );
    v___x_1009_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1009_, 0, v___x_1008_);
    crate::leanh::lean_ctor_set(v___x_1009_, 1, v___x_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v_int_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_int_1010_ = l_Lean_Int_mkType;
    v___x_1011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__10,
    );
    v___x_1012_ = l_Lean_mkApp3(v___x_1011_, v_int_1010_, v_int_1010_, v_int_1010_);
    return v___x_1012_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Lean_Int_mkInstHSub;
    v___x_1014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__47,
    );
    v___x_1015_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1015_, 0, v___x_1014_);
    crate::leanh::lean_ctor_set(v___x_1015_, 1, v___x_1013_);
    return v___x_1015_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49()
-> *mut crate::leanh::LeanObject {
    let mut v_int_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_int_1016_ = l_Lean_Int_mkType;
    v___x_1017_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__15,
    );
    v___x_1018_ = l_Lean_mkApp3(v___x_1017_, v_int_1016_, v_int_1016_, v_int_1016_);
    return v___x_1018_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_Lean_Int_mkInstHMul;
    v___x_1020_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__49,
    );
    v___x_1021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1021_, 0, v___x_1020_);
    crate::leanh::lean_ctor_set(v___x_1021_, 1, v___x_1019_);
    return v___x_1021_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v_int_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_int_1022_ = l_Lean_Int_mkType;
    v___x_1023_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__20,
    );
    v___x_1024_ = l_Lean_mkApp3(v___x_1023_, v_int_1022_, v_int_1022_, v_int_1022_);
    return v___x_1024_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l_Lean_Int_mkInstHDiv;
    v___x_1026_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__51,
    );
    v___x_1027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    crate::leanh::lean_ctor_set(v___x_1027_, 1, v___x_1025_);
    return v___x_1027_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53()
-> *mut crate::leanh::LeanObject {
    let mut v_int_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_int_1028_ = l_Lean_Int_mkType;
    v___x_1029_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__25,
    );
    v___x_1030_ = l_Lean_mkApp3(v___x_1029_, v_int_1028_, v_int_1028_, v_int_1028_);
    return v___x_1030_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = l_Lean_Int_mkInstHMod;
    v___x_1032_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__53,
    );
    v___x_1033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1033_, 0, v___x_1032_);
    crate::leanh::lean_ctor_set(v___x_1033_, 1, v___x_1031_);
    return v___x_1033_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55()
-> *mut crate::leanh::LeanObject {
    let mut v_nat_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_int_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nat_1034_ = l_Lean_Nat_mkType;
    v_int_1035_ = l_Lean_Int_mkType;
    v___x_1036_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__30,
    );
    v___x_1037_ = l_Lean_mkApp3(v___x_1036_, v_int_1035_, v_nat_1034_, v_int_1035_);
    return v___x_1037_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = l_Lean_Int_mkInstHPow;
    v___x_1039_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__55,
    );
    v___x_1040_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1040_, 0, v___x_1039_);
    crate::leanh::lean_ctor_set(v___x_1040_, 1, v___x_1038_);
    return v___x_1040_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v_int_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_int_1041_ = l_Lean_Int_mkType;
    v___x_1042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__37,
    );
    v___x_1043_ = l_Lean_Expr_app___override(v___x_1042_, v_int_1041_);
    return v___x_1043_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = l_Lean_Int_mkInstLT;
    v___x_1045_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__57,
    );
    v___x_1046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1046_, 0, v___x_1045_);
    crate::leanh::lean_ctor_set(v___x_1046_, 1, v___x_1044_);
    return v___x_1046_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59()
-> *mut crate::leanh::LeanObject {
    let mut v_int_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_int_1047_ = l_Lean_Int_mkType;
    v___x_1048_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__42,
    );
    v___x_1049_ = l_Lean_Expr_app___override(v___x_1048_, v_int_1047_);
    return v___x_1049_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = l_Lean_Int_mkInstLE;
    v___x_1051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__59,
    );
    v___x_1052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1052_, 0, v___x_1051_);
    crate::leanh::lean_ctor_set(v___x_1052_, 1, v___x_1050_);
    return v___x_1052_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = crate::leanh::lean_box(0);
    v___x_1054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__60,
    );
    v___x_1055_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1055_, 0, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 1, v___x_1053_);
    return v___x_1055_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1056_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__61,
    );
    v___x_1057_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__58,
    );
    v___x_1058_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1058_, 0, v___x_1057_);
    crate::leanh::lean_ctor_set(v___x_1058_, 1, v___x_1056_);
    return v___x_1058_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__62,
    );
    v___x_1060_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__56,
    );
    v___x_1061_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1061_, 0, v___x_1060_);
    crate::leanh::lean_ctor_set(v___x_1061_, 1, v___x_1059_);
    return v___x_1061_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__63,
    );
    v___x_1063_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__54,
    );
    v___x_1064_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1064_, 0, v___x_1063_);
    crate::leanh::lean_ctor_set(v___x_1064_, 1, v___x_1062_);
    return v___x_1064_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1065_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__64,
    );
    v___x_1066_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__52,
    );
    v___x_1067_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1067_, 0, v___x_1066_);
    crate::leanh::lean_ctor_set(v___x_1067_, 1, v___x_1065_);
    return v___x_1067_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__65,
    );
    v___x_1069_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__50,
    );
    v___x_1070_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1070_, 0, v___x_1069_);
    crate::leanh::lean_ctor_set(v___x_1070_, 1, v___x_1068_);
    return v___x_1070_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__66,
    );
    v___x_1072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__48,
    );
    v___x_1073_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1072_);
    crate::leanh::lean_ctor_set(v___x_1073_, 1, v___x_1071_);
    return v___x_1073_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__67,
    );
    v___x_1075_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__46,
    );
    v___x_1076_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1076_, 0, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1076_, 1, v___x_1074_);
    return v___x_1076_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__68,
    );
    v___x_1078_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__44,
    );
    v___x_1079_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    crate::leanh::lean_ctor_set(v___x_1079_, 1, v___x_1077_);
    return v___x_1079_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__69,
    );
    v___x_1081_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__39,
    );
    v___x_1082_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1082_, 0, v___x_1081_);
    crate::leanh::lean_ctor_set(v___x_1082_, 1, v___x_1080_);
    return v___x_1082_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__70,
    );
    v___x_1084_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__32,
    );
    v___x_1085_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1085_, 0, v___x_1084_);
    crate::leanh::lean_ctor_set(v___x_1085_, 1, v___x_1083_);
    return v___x_1085_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__71,
    );
    v___x_1087_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__27,
    );
    v___x_1088_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1088_, 0, v___x_1087_);
    crate::leanh::lean_ctor_set(v___x_1088_, 1, v___x_1086_);
    return v___x_1088_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__72,
    );
    v___x_1090_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__22,
    );
    v___x_1091_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1091_, 0, v___x_1090_);
    crate::leanh::lean_ctor_set(v___x_1091_, 1, v___x_1089_);
    return v___x_1091_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__73,
    );
    v___x_1093_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__17,
    );
    v___x_1094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1093_);
    crate::leanh::lean_ctor_set(v___x_1094_, 1, v___x_1092_);
    return v___x_1094_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__74,
    );
    v___x_1096_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__12,
    );
    v___x_1097_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1097_, 0, v___x_1096_);
    crate::leanh::lean_ctor_set(v___x_1097_, 1, v___x_1095_);
    return v___x_1097_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__75,
    );
    v___x_1099_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__7,
    );
    v___x_1100_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1099_);
    crate::leanh::lean_ctor_set(v___x_1100_, 1, v___x_1098_);
    return v___x_1100_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = crate::leanh::lean_box(0);
    v___x_1102_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1103_ = lean_mk_array(v___x_1102_, v___x_1101_);
    return v___x_1103_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__77,
    );
    v___x_1105_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1106_, 0, v___x_1105_);
    crate::leanh::lean_ctor_set(v___x_1106_, 1, v___x_1104_);
    return v___x_1106_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__78,
    );
    v___x_1108_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__76,
    );
    v___x_1109_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v___x_1108_, v___x_1107_);
    return v___x_1109_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79_once
        ),
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts___closed__79,
    );
    return v___x_1110_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0(
    mut v_00_u03b2_1111_: *mut crate::leanh::LeanObject,
    mut v_m_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_b_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0___redArg(v_m_1112_, v_a_1113_, v_b_1114_);
    return v___x_1115_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1(
    mut v_as_1116_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1117_: *mut crate::leanh::LeanObject,
    mut v_b_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___redArg(v_as_x27_1117_, v_b_1118_);
    return v___x_1120_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1___boxed(
    mut v_as_1121_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1122_: *mut crate::leanh::LeanObject,
    mut v_b_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__1(v_as_1121_, v_as_x27_1122_, v_b_1123_, v_a_1124_);
    crate::leanh::lean_dec(v_as_x27_1122_);
    crate::leanh::lean_dec(v_as_1121_);
    return v_res_1125_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_x_1128_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1129_: u8 = 0;
    v___x_1129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___redArg(v_a_1127_, v_x_1128_);
    return v___x_1129_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_x_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1133_: u8 = 0;
    let mut v_r_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__1(v_00_u03b2_1130_, v_a_1131_, v_x_1132_);
    crate::leanh::lean_dec(v_x_1132_);
    crate::leanh::lean_dec_ref(v_a_1131_);
    v_r_1134_ = crate::leanh::lean_box((v_res_1133_) as usize);
    return v_r_1134_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1135_: *mut crate::leanh::LeanObject,
    mut v_data_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2___redArg(v_data_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1138_: *mut crate::leanh::LeanObject,
    mut v_a_1139_: *mut crate::leanh::LeanObject,
    mut v_b_1140_: *mut crate::leanh::LeanObject,
    mut v_x_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__3___redArg(v_a_1139_, v_b_1140_, v_x_1141_);
    return v___x_1142_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_1143_: *mut crate::leanh::LeanObject,
    mut v_i_1144_: *mut crate::leanh::LeanObject,
    mut v_source_1145_: *mut crate::leanh::LeanObject,
    mut v_target_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1147_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3___redArg(v_i_1144_, v_source_1145_, v_target_1146_);
    return v___x_1147_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1148_: *mut crate::leanh::LeanObject,
    mut v_x_1149_: *mut crate::leanh::LeanObject,
    mut v_x_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1151_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_1149_, v_x_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_x_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: u8 = 0;
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1153_) == 0 {
                    v___x_1154_ = crate::leanh::lean_box(0);
                    return v___x_1154_;
                } else {
                    v_key_1155_ = crate::leanh::lean_ctor_get(v_x_1153_, 0);
                    v_value_1156_ = crate::leanh::lean_ctor_get(v_x_1153_, 1);
                    v_tail_1157_ = crate::leanh::lean_ctor_get(v_x_1153_, 2);
                    v___x_1158_ = lean_expr_eqv(v_key_1155_, v_a_1152_);
                    if v___x_1158_ == 0 {
                        v_x_1153_ = v_tail_1157_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1156_);
                        v___x_1160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1160_, 0, v_value_1156_);
                        return v___x_1160_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_1161_: *mut crate::leanh::LeanObject,
    mut v_x_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_1161_, v_x_1162_);
    crate::leanh::lean_dec(v_x_1162_);
    crate::leanh::lean_dec_ref(v_a_1161_);
    return v_res_1163_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(
    mut v_m_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u64 = 0;
    let mut v___x_1169_: u64 = 0;
    let mut v___x_1170_: u64 = 0;
    let mut v_fold_1171_: u64 = 0;
    let mut v___x_1172_: u64 = 0;
    let mut v___x_1173_: u64 = 0;
    let mut v___x_1174_: u64 = 0;
    let mut v___x_1175_: usize = 0;
    let mut v___x_1176_: usize = 0;
    let mut v___x_1177_: usize = 0;
    let mut v___x_1178_: usize = 0;
    let mut v___x_1179_: usize = 0;
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1166_ = crate::leanh::lean_ctor_get(v_m_1164_, 1);
    v___x_1167_ = lean_array_get_size(v_buckets_1166_);
    v___x_1168_ = l_Lean_Expr_hash(v_a_1165_);
    v___x_1169_ = 32u64;
    v___x_1170_ = lean_uint64_shift_right(v___x_1168_, v___x_1169_);
    v_fold_1171_ = lean_uint64_xor(v___x_1168_, v___x_1170_);
    v___x_1172_ = 16u64;
    v___x_1173_ = lean_uint64_shift_right(v_fold_1171_, v___x_1172_);
    v___x_1174_ = lean_uint64_xor(v_fold_1171_, v___x_1173_);
    v___x_1175_ = lean_uint64_to_usize(v___x_1174_);
    v___x_1176_ = lean_usize_of_nat(v___x_1167_);
    v___x_1177_ = 1usize;
    v___x_1178_ = lean_usize_sub(v___x_1176_, v___x_1177_);
    v___x_1179_ = lean_usize_land(v___x_1175_, v___x_1178_);
    v___x_1180_ = lean_array_uget_borrowed(v_buckets_1166_, v___x_1179_);
    v___x_1181_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_1165_, v___x_1180_);
    return v___x_1181_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg___boxed(
    mut v_m_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_1182_, v_a_1183_);
    crate::leanh::lean_dec_ref(v_a_1183_);
    crate::leanh::lean_dec_ref(v_m_1182_);
    return v_res_1184_;
}
pub unsafe fn l_Lean_Meta_Sym_getBuiltinInstance_x3f(
    mut v_type_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1186_ = l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts;
    v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v___x_1186_, v_type_1185_);
    return v___x_1187_;
}
pub unsafe fn l_Lean_Meta_Sym_getBuiltinInstance_x3f___boxed(
    mut v_type_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_type_1188_);
    crate::leanh::lean_dec_ref(v_type_1188_);
    return v_res_1189_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(
    mut v_00_u03b2_1190_: *mut crate::leanh::LeanObject,
    mut v_m_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___redArg(v_m_1191_, v_a_1192_);
    return v___x_1193_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0___boxed(
    mut v_00_u03b2_1194_: *mut crate::leanh::LeanObject,
    mut v_m_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0(v_00_u03b2_1194_, v_m_1195_, v_a_1196_);
    crate::leanh::lean_dec_ref(v_a_1196_);
    crate::leanh::lean_dec_ref(v_m_1195_);
    return v_res_1197_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(
    mut v_00_u03b2_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_x_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___redArg(v_a_1199_, v_x_1200_);
    return v___x_1201_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1202_: *mut crate::leanh::LeanObject,
    mut v_a_1203_: *mut crate::leanh::LeanObject,
    mut v_x_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_getBuiltinInstance_x3f_spec__0_spec__0(v_00_u03b2_1202_, v_a_1203_, v_x_1204_);
    crate::leanh::lean_dec(v_x_1204_);
    crate::leanh::lean_dec_ref(v_a_1203_);
    return v_res_1205_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(
    mut v_category_1206_: *mut crate::leanh::LeanObject,
    mut v_opts_1207_: *mut crate::leanh::LeanObject,
    mut v_act_1208_: *mut crate::leanh::LeanObject,
    mut v_decl_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1213_);
    crate::leanh::lean_inc_ref(v___y_1212_);
    crate::leanh::lean_inc(v___y_1211_);
    crate::leanh::lean_inc_ref(v___y_1210_);
    v___x_1215_ = crate::leanh::lean_apply_4(
        v_act_1208_,
        v___y_1210_,
        v___y_1211_,
        v___y_1212_,
        v___y_1213_,
    );
    v___x_1216_ = l_Lean_profileitIOUnsafe___redArg(
        v_category_1206_,
        v_opts_1207_,
        v___x_1215_,
        v_decl_1209_,
    );
    return v___x_1216_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg___boxed(
    mut v_category_1217_: *mut crate::leanh::LeanObject,
    mut v_opts_1218_: *mut crate::leanh::LeanObject,
    mut v_act_1219_: *mut crate::leanh::LeanObject,
    mut v_decl_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(
        v_category_1217_,
        v_opts_1218_,
        v_act_1219_,
        v_decl_1220_,
        v___y_1221_,
        v___y_1222_,
        v___y_1223_,
        v___y_1224_,
    );
    crate::leanh::lean_dec(v___y_1224_);
    crate::leanh::lean_dec_ref(v___y_1223_);
    crate::leanh::lean_dec(v___y_1222_);
    crate::leanh::lean_dec_ref(v___y_1221_);
    crate::leanh::lean_dec_ref(v_opts_1218_);
    crate::leanh::lean_dec_ref(v_category_1217_);
    return v_res_1226_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(
    mut v_00_u03b1_1227_: *mut crate::leanh::LeanObject,
    mut v_category_1228_: *mut crate::leanh::LeanObject,
    mut v_opts_1229_: *mut crate::leanh::LeanObject,
    mut v_act_1230_: *mut crate::leanh::LeanObject,
    mut v_decl_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(
        v_category_1228_,
        v_opts_1229_,
        v_act_1230_,
        v_decl_1231_,
        v___y_1232_,
        v___y_1233_,
        v___y_1234_,
        v___y_1235_,
    );
    return v___x_1237_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___boxed(
    mut v_00_u03b1_1238_: *mut crate::leanh::LeanObject,
    mut v_category_1239_: *mut crate::leanh::LeanObject,
    mut v_opts_1240_: *mut crate::leanh::LeanObject,
    mut v_act_1241_: *mut crate::leanh::LeanObject,
    mut v_decl_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0(
        v_00_u03b1_1238_,
        v_category_1239_,
        v_opts_1240_,
        v_act_1241_,
        v_decl_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
        v___y_1246_,
    );
    crate::leanh::lean_dec(v___y_1246_);
    crate::leanh::lean_dec_ref(v___y_1245_);
    crate::leanh::lean_dec(v___y_1244_);
    crate::leanh::lean_dec_ref(v___y_1243_);
    crate::leanh::lean_dec_ref(v_opts_1240_);
    crate::leanh::lean_dec_ref(v_category_1239_);
    return v_res_1248_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(
    mut v___x_1249_: *mut crate::leanh::LeanObject,
    mut v_type_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1262_: u8 = 0;
    let mut v_id_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_unused_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut v___x_1274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___x_1249_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_1250_);
                    v___x_1256_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1249_);
                    return v___x_1256_;
                } else {
                    crate::leanh::lean_dec(v___x_1249_);
                    v___x_1257_ = crate::leanh::lean_box(0);
                    v___x_1258_ = l_Lean_Meta_synthInstanceCore_x3f(
                        v_type_1250_,
                        v___x_1257_,
                        v___y_1251_,
                        v___y_1252_,
                        v___y_1253_,
                        v___y_1254_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1258_) == 0 {
                        return v___x_1258_;
                    } else {
                        v_a_1259_ = crate::leanh::lean_ctor_get(v___x_1258_, 0);
                        crate::leanh::lean_inc(v_a_1259_);
                        v___x_1260_ = l_Lean_Meta_isDefEqStuckExceptionId;
                        v___x_1273_ = l_Lean_Exception_isInterrupt(v_a_1259_);
                        if v___x_1273_ == 0 {
                            crate::leanh::lean_inc(v_a_1259_);
                            v___x_1274_ = l_Lean_Exception_isRuntime(v_a_1259_);
                            v___y_1262_ = v___x_1274_;
                            state = 1;
                            continue;
                        } else {
                            v___y_1262_ = v___x_1273_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_1262_ == 0 {
                    if crate::leanh::lean_obj_tag(v_a_1259_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_1259_, 2);
                        return v___x_1258_;
                    } else {
                        v_id_1263_ = crate::leanh::lean_ctor_get(v_a_1259_, 0);
                        crate::leanh::lean_inc(v_id_1263_);
                        crate::leanh::lean_dec_ref_known(v_a_1259_, 2);
                        v___x_1264_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_1260_, v_id_1263_);
                        crate::leanh::lean_dec(v_id_1263_);
                        if v___x_1264_ == 0 {
                            return v___x_1258_;
                        } else {
                            v_isSharedCheck_1271_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1258_)) as u8;
                            if v_isSharedCheck_1271_ == 0 {
                                v_unused_1272_ = crate::leanh::lean_ctor_get(v___x_1258_, 0);
                                crate::leanh::lean_dec(v_unused_1272_);
                                v___x_1266_ = v___x_1258_;
                                v_isShared_1267_ = v_isSharedCheck_1271_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1258_);
                                v___x_1266_ = crate::leanh::lean_box(0);
                                v_isShared_1267_ = v_isSharedCheck_1271_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1259_);
                    return v___x_1258_;
                }
            }
            2 => {
                if v_isShared_1267_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1266_, 0);
                    crate::leanh::lean_ctor_set(v___x_1266_, 0, v___x_1257_);
                    v___x_1269_ = v___x_1266_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1257_);
                    v___x_1269_ = v_reuseFailAlloc_1270_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed(
    mut v___x_1275_: *mut crate::leanh::LeanObject,
    mut v_type_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1282_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0(
        v___x_1275_,
        v_type_1276_,
        v___y_1277_,
        v___y_1278_,
        v___y_1279_,
        v___y_1280_,
    );
    crate::leanh::lean_dec(v___y_1280_);
    crate::leanh::lean_dec_ref(v___y_1279_);
    crate::leanh::lean_dec(v___y_1278_);
    crate::leanh::lean_dec_ref(v___y_1277_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceMeta_x3f(
    mut v_type_1284_: *mut crate::leanh::LeanObject,
    mut v_a_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_1290_ = crate::leanh::lean_ctor_get(v_a_1287_, 2);
    v___x_1291_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f___closed__0;
    v___x_1292_ = l_Lean_Meta_Sym_getBuiltinInstance_x3f(v_type_1284_);
    crate::leanh::lean_inc_ref(v_type_1284_);
    v___y_1293_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_synthInstanceMeta_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___y_1293_, 0, v___x_1292_);
    crate::leanh::lean_closure_set(v___y_1293_, 1, v_type_1284_);
    v___x_1294_ = l_Lean_Expr_getAppFn(v_type_1284_);
    crate::leanh::lean_dec_ref(v_type_1284_);
    v___x_1295_ = l_Lean_Expr_constName_x3f(v___x_1294_);
    crate::leanh::lean_dec_ref(v___x_1294_);
    if crate::leanh::lean_obj_tag(v___x_1295_) == 0 {
        let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1296_ = crate::leanh::lean_box(0);
        v___x_1297_ =
            l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(
                v___x_1291_,
                v_options_1290_,
                v___y_1293_,
                v___x_1296_,
                v_a_1285_,
                v_a_1286_,
                v_a_1287_,
                v_a_1288_,
            );
        return v___x_1297_;
    } else {
        let mut v_val_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1298_ = crate::leanh::lean_ctor_get(v___x_1295_, 0);
        crate::leanh::lean_inc(v_val_1298_);
        crate::leanh::lean_dec_ref_known(v___x_1295_, 1);
        v___x_1299_ =
            l_Lean_profileitM___at___00Lean_Meta_Sym_synthInstanceMeta_x3f_spec__0___redArg(
                v___x_1291_,
                v_options_1290_,
                v___y_1293_,
                v_val_1298_,
                v_a_1285_,
                v_a_1286_,
                v_a_1287_,
                v_a_1288_,
            );
        return v___x_1299_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceMeta_x3f___boxed(
    mut v_type_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
    mut v_a_1302_: *mut crate::leanh::LeanObject,
    mut v_a_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_a_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_type_1300_,
        v_a_1301_,
        v_a_1302_,
        v_a_1303_,
        v_a_1304_,
    );
    crate::leanh::lean_dec(v_a_1304_);
    crate::leanh::lean_dec_ref(v_a_1303_);
    crate::leanh::lean_dec(v_a_1302_);
    crate::leanh::lean_dec_ref(v_a_1301_);
    return v_res_1306_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstance_x3f___redArg(
    mut v_type_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_type_1307_,
        v_a_1308_,
        v_a_1309_,
        v_a_1310_,
        v_a_1311_,
    );
    return v___x_1313_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstance_x3f___redArg___boxed(
    mut v_type_1314_: *mut crate::leanh::LeanObject,
    mut v_a_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(
        v_type_1314_,
        v_a_1315_,
        v_a_1316_,
        v_a_1317_,
        v_a_1318_,
    );
    crate::leanh::lean_dec(v_a_1318_);
    crate::leanh::lean_dec_ref(v_a_1317_);
    crate::leanh::lean_dec(v_a_1316_);
    crate::leanh::lean_dec_ref(v_a_1315_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstance_x3f(
    mut v_type_1321_: *mut crate::leanh::LeanObject,
    mut v_a_1322_: *mut crate::leanh::LeanObject,
    mut v_a_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_type_1321_,
        v_a_1324_,
        v_a_1325_,
        v_a_1326_,
        v_a_1327_,
    );
    return v___x_1329_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstance_x3f___boxed(
    mut v_type_1330_: *mut crate::leanh::LeanObject,
    mut v_a_1331_: *mut crate::leanh::LeanObject,
    mut v_a_1332_: *mut crate::leanh::LeanObject,
    mut v_a_1333_: *mut crate::leanh::LeanObject,
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
    mut v_a_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1338_ = l_Lean_Meta_Sym_synthInstance_x3f(
        v_type_1330_,
        v_a_1331_,
        v_a_1332_,
        v_a_1333_,
        v_a_1334_,
        v_a_1335_,
        v_a_1336_,
    );
    crate::leanh::lean_dec(v_a_1336_);
    crate::leanh::lean_dec_ref(v_a_1335_);
    crate::leanh::lean_dec(v_a_1334_);
    crate::leanh::lean_dec_ref(v_a_1333_);
    crate::leanh::lean_dec(v_a_1332_);
    crate::leanh::lean_dec_ref(v_a_1331_);
    return v_res_1338_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(
    mut v_msgData_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = lean_st_ref_get(v___y_1343_);
    v_env_1346_ = crate::leanh::lean_ctor_get(v___x_1345_, 0);
    crate::leanh::lean_inc_ref(v_env_1346_);
    crate::leanh::lean_dec(v___x_1345_);
    v___x_1347_ = lean_st_ref_get(v___y_1341_);
    v_mctx_1348_ = crate::leanh::lean_ctor_get(v___x_1347_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1348_);
    crate::leanh::lean_dec(v___x_1347_);
    v_lctx_1349_ = crate::leanh::lean_ctor_get(v___y_1340_, 2);
    v_options_1350_ = crate::leanh::lean_ctor_get(v___y_1342_, 2);
    crate::leanh::lean_inc_ref(v_options_1350_);
    crate::leanh::lean_inc_ref(v_lctx_1349_);
    v___x_1351_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1351_, 0, v_env_1346_);
    crate::leanh::lean_ctor_set(v___x_1351_, 1, v_mctx_1348_);
    crate::leanh::lean_ctor_set(v___x_1351_, 2, v_lctx_1349_);
    crate::leanh::lean_ctor_set(v___x_1351_, 3, v_options_1350_);
    v___x_1352_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1352_, 0, v___x_1351_);
    crate::leanh::lean_ctor_set(v___x_1352_, 1, v_msgData_1339_);
    v___x_1353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1353_, 0, v___x_1352_);
    return v___x_1353_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0___boxed(
    mut v_msgData_1354_: *mut crate::leanh::LeanObject,
    mut v___y_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1360_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msgData_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
    crate::leanh::lean_dec(v___y_1358_);
    crate::leanh::lean_dec_ref(v___y_1357_);
    crate::leanh::lean_dec(v___y_1356_);
    crate::leanh::lean_dec_ref(v___y_1355_);
    return v_res_1360_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(
    mut v_msg_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1367_ = crate::leanh::lean_ctor_get(v___y_1364_, 5);
                v___x_1368_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0_spec__0(v_msg_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
                v_a_1369_ = crate::leanh::lean_ctor_get(v___x_1368_, 0);
                v_isSharedCheck_1377_ = (!crate::leanh::lean_is_exclusive(v___x_1368_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v___x_1371_ = v___x_1368_;
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1369_);
                    crate::leanh::lean_dec(v___x_1368_);
                    v___x_1371_ = crate::leanh::lean_box(0);
                    v_isShared_1372_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1367_);
                v___x_1373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1373_, 0, v_ref_1367_);
                crate::leanh::lean_ctor_set(v___x_1373_, 1, v_a_1369_);
                if v_isShared_1372_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1371_, 1);
                    crate::leanh::lean_ctor_set(v___x_1371_, 0, v___x_1373_);
                    v___x_1375_ = v___x_1371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
                    v___x_1375_ = v_reuseFailAlloc_1376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg___boxed(
    mut v_msg_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(
        v_msg_1378_,
        v___y_1379_,
        v___y_1380_,
        v___y_1381_,
        v___y_1382_,
    );
    crate::leanh::lean_dec(v___y_1382_);
    crate::leanh::lean_dec_ref(v___y_1381_);
    crate::leanh::lean_dec(v___y_1380_);
    crate::leanh::lean_dec_ref(v___y_1379_);
    return v_res_1384_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_synthInstance___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Lean_Meta_Sym_synthInstance___closed__0;
    v___x_1387_ = l_Lean_stringToMessageData(v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstance(
    mut v_type_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
    mut v_a_1394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v_val_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1409_: u8 = 0;
    let mut v_a_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_1388_);
                v___x_1396_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_1388_,
                    v_a_1391_,
                    v_a_1392_,
                    v_a_1393_,
                    v_a_1394_,
                );
                if crate::leanh::lean_obj_tag(v___x_1396_) == 0 {
                    v_a_1397_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                    v_isSharedCheck_1409_ = (!crate::leanh::lean_is_exclusive(v___x_1396_)) as u8;
                    if v_isSharedCheck_1409_ == 0 {
                        v___x_1399_ = v___x_1396_;
                        v_isShared_1400_ = v_isSharedCheck_1409_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1397_);
                        crate::leanh::lean_dec(v___x_1396_);
                        v___x_1399_ = crate::leanh::lean_box(0);
                        v_isShared_1400_ = v_isSharedCheck_1409_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_1388_);
                    v_a_1410_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                    v_isSharedCheck_1417_ = (!crate::leanh::lean_is_exclusive(v___x_1396_)) as u8;
                    if v_isSharedCheck_1417_ == 0 {
                        v___x_1412_ = v___x_1396_;
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1410_);
                        crate::leanh::lean_dec(v___x_1396_);
                        v___x_1412_ = crate::leanh::lean_box(0);
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1397_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_1388_);
                    v_val_1401_ = crate::leanh::lean_ctor_get(v_a_1397_, 0);
                    crate::leanh::lean_inc(v_val_1401_);
                    crate::leanh::lean_dec_ref_known(v_a_1397_, 1);
                    if v_isShared_1400_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1399_, 0, v_val_1401_);
                        v___x_1403_ = v___x_1399_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1404_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_val_1401_);
                        v___x_1403_ = v_reuseFailAlloc_1404_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1399_);
                    crate::leanh::lean_dec(v_a_1397_);
                    v___x_1405_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_synthInstance___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_synthInstance___closed__1_once),
                        _init_l_Lean_Meta_Sym_synthInstance___closed__1,
                    );
                    v___x_1406_ = l_Lean_indentExpr(v_type_1388_);
                    v___x_1407_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1407_, 0, v___x_1405_);
                    crate::leanh::lean_ctor_set(v___x_1407_, 1, v___x_1406_);
                    v___x_1408_ =
                        l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(
                            v___x_1407_,
                            v_a_1391_,
                            v_a_1392_,
                            v_a_1393_,
                            v_a_1394_,
                        );
                    return v___x_1408_;
                }
            }
            2 => {
                return v___x_1403_;
            }
            3 => {
                if v_isShared_1413_ == 0 {
                    v___x_1415_ = v___x_1412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1416_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_synthInstance___boxed(
    mut v_type_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
    mut v_a_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_Lean_Meta_Sym_synthInstance(
        v_type_1418_,
        v_a_1419_,
        v_a_1420_,
        v_a_1421_,
        v_a_1422_,
        v_a_1423_,
        v_a_1424_,
    );
    crate::leanh::lean_dec(v_a_1424_);
    crate::leanh::lean_dec_ref(v_a_1423_);
    crate::leanh::lean_dec(v_a_1422_);
    crate::leanh::lean_dec_ref(v_a_1421_);
    crate::leanh::lean_dec(v_a_1420_);
    crate::leanh::lean_dec_ref(v_a_1419_);
    return v_res_1426_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(
    mut v_00_u03b1_1427_: *mut crate::leanh::LeanObject,
    mut v_msg_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___redArg(
        v_msg_1428_,
        v___y_1431_,
        v___y_1432_,
        v___y_1433_,
        v___y_1434_,
    );
    return v___x_1436_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0___boxed(
    mut v_00_u03b1_1437_: *mut crate::leanh::LeanObject,
    mut v_msg_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Lean_throwError___at___00Lean_Meta_Sym_synthInstance_spec__0(
        v_00_u03b1_1437_,
        v_msg_1438_,
        v___y_1439_,
        v___y_1440_,
        v___y_1441_,
        v___y_1442_,
        v___y_1443_,
        v___y_1444_,
    );
    crate::leanh::lean_dec(v___y_1444_);
    crate::leanh::lean_dec_ref(v___y_1443_);
    crate::leanh::lean_dec(v___y_1442_);
    crate::leanh::lean_dec_ref(v___y_1441_);
    crate::leanh::lean_dec(v___y_1440_);
    crate::leanh::lean_dec_ref(v___y_1439_);
    return v_res_1446_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(
    mut v_x_1447_: *mut crate::leanh::LeanObject,
    mut v_type_1448_: *mut crate::leanh::LeanObject,
    mut v_a_1449_: *mut crate::leanh::LeanObject,
    mut v_a_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
    mut v_a_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v_val_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1466_: u8 = 0;
    let mut v_a_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1454_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_1448_,
                    v_a_1449_,
                    v_a_1450_,
                    v_a_1451_,
                    v_a_1452_,
                );
                if crate::leanh::lean_obj_tag(v___x_1454_) == 0 {
                    v_a_1455_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                    v_isSharedCheck_1466_ = (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                    if v_isSharedCheck_1466_ == 0 {
                        v___x_1457_ = v___x_1454_;
                        v_isShared_1458_ = v_isSharedCheck_1466_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1455_);
                        crate::leanh::lean_dec(v___x_1454_);
                        v___x_1457_ = crate::leanh::lean_box(0);
                        v_isShared_1458_ = v_isSharedCheck_1466_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1447_);
                    v_a_1467_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                    v_isSharedCheck_1474_ = (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                    if v_isSharedCheck_1474_ == 0 {
                        v___x_1469_ = v___x_1454_;
                        v_isShared_1470_ = v_isSharedCheck_1474_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1467_);
                        crate::leanh::lean_dec(v___x_1454_);
                        v___x_1469_ = crate::leanh::lean_box(0);
                        v_isShared_1470_ = v_isSharedCheck_1474_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1455_) == 1 {
                    crate::leanh::lean_del_object(v___x_1457_);
                    v_val_1459_ = crate::leanh::lean_ctor_get(v_a_1455_, 0);
                    crate::leanh::lean_inc(v_val_1459_);
                    crate::leanh::lean_dec_ref_known(v_a_1455_, 1);
                    v___x_1460_ = l_Lean_Meta_isExprDefEq(
                        v_x_1447_,
                        v_val_1459_,
                        v_a_1449_,
                        v_a_1450_,
                        v_a_1451_,
                        v_a_1452_,
                    );
                    return v___x_1460_;
                } else {
                    crate::leanh::lean_dec(v_a_1455_);
                    crate::leanh::lean_dec_ref(v_x_1447_);
                    v___x_1461_ = 0;
                    v___x_1462_ = crate::leanh::lean_box((v___x_1461_) as usize);
                    if v_isShared_1458_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1462_);
                        v___x_1464_ = v___x_1457_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
                        v___x_1464_ = v_reuseFailAlloc_1465_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1464_;
            }
            3 => {
                if v_isShared_1470_ == 0 {
                    v___x_1472_ = v___x_1469_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
                    v___x_1472_ = v_reuseFailAlloc_1473_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceAndAssign___redArg___boxed(
    mut v_x_1475_: *mut crate::leanh::LeanObject,
    mut v_type_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
    mut v_a_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(
        v_x_1475_,
        v_type_1476_,
        v_a_1477_,
        v_a_1478_,
        v_a_1479_,
        v_a_1480_,
    );
    crate::leanh::lean_dec(v_a_1480_);
    crate::leanh::lean_dec_ref(v_a_1479_);
    crate::leanh::lean_dec(v_a_1478_);
    crate::leanh::lean_dec_ref(v_a_1477_);
    return v_res_1482_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceAndAssign(
    mut v_x_1483_: *mut crate::leanh::LeanObject,
    mut v_type_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v_a_1487_: *mut crate::leanh::LeanObject,
    mut v_a_1488_: *mut crate::leanh::LeanObject,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
    mut v_a_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(
        v_x_1483_,
        v_type_1484_,
        v_a_1487_,
        v_a_1488_,
        v_a_1489_,
        v_a_1490_,
    );
    return v___x_1492_;
}
pub unsafe fn l_Lean_Meta_Sym_synthInstanceAndAssign___boxed(
    mut v_x_1493_: *mut crate::leanh::LeanObject,
    mut v_type_1494_: *mut crate::leanh::LeanObject,
    mut v_a_1495_: *mut crate::leanh::LeanObject,
    mut v_a_1496_: *mut crate::leanh::LeanObject,
    mut v_a_1497_: *mut crate::leanh::LeanObject,
    mut v_a_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_Meta_Sym_synthInstanceAndAssign(
        v_x_1493_,
        v_type_1494_,
        v_a_1495_,
        v_a_1496_,
        v_a_1497_,
        v_a_1498_,
        v_a_1499_,
        v_a_1500_,
    );
    crate::leanh::lean_dec(v_a_1500_);
    crate::leanh::lean_dec_ref(v_a_1499_);
    crate::leanh::lean_dec(v_a_1498_);
    crate::leanh::lean_dec_ref(v_a_1497_);
    crate::leanh::lean_dec(v_a_1496_);
    crate::leanh::lean_dec_ref(v_a_1495_);
    return v_res_1502_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_SynthInstance(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts =
        _init_l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Sym_SynthInstance_0__Lean_Meta_Sym_builtinInsts,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_SynthInstance(
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
pub unsafe fn initialize_Lean_Meta_Sym_SynthInstance(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_SynthInstance(builtin);
}
